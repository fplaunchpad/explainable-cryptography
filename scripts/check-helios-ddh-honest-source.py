#!/usr/bin/env python3
"""Independent multiplicative programmed-pair controls on fixed coin tapes.
Compares full proof/decision/cache traces, not all election distributions.
"""
from collections import Counter
import hashlib
import copy
import json
import random

P,Q,G,PK = 23,11,2,8

def enc(r,m):
    return pow(G,r % Q,P), pow(G,m % Q,P)*pow(PK,r % Q,P) % P

def mul(a,b):
    return tuple(x*y % P for x,y in zip(a,b))

def div(a,b):
    return tuple(x*pow(y,-1,P) % P for x,y in zip(a,b))

def transcript(ct,coins):
    c,e,z0,z1=coins
    proof=[]
    for m,z,d in ((0,z0,e),(1,z1,(c-e) % Q)):
        a=pow(G,z,P)*pow(pow(ct[0],d,P),-1,P) % P
        v=ct[1]*pow(pow(G,m,P),-1,P) % P
        b=pow(PK,z,P)*pow(pow(v,d,P),-1,P) % P
        proof.append((a,b,d,z))
    return tuple(proof),c

def key(ct,proof):
    return ct,tuple(p[:2] for p in proof)

def valid(ct,proof,c):
    if sum(p[2] for p in proof) % Q != c:
        return False
    return all(pow(G,z,P)==a*pow(ct[0],d,P)%P and
               pow(PK,z,P)==b*pow(ct[1]*pow(pow(G,m,P),-1,P)%P,d,P)%P
               for m,(a,b,d,z) in enumerate(proof))

def execute(vote,nonces,coins,initial,initial_bad,challenge=False,mutation=None,vectors=None):
    x,a,y,b=nonces
    if vectors is not None:
        pass
    elif challenge:
        c=(pow(G,x,P),pow(G,vote,P)*pow(PK,x,P)%P)
        vectors=((c,enc(a,0)),(div(enc(x+y,1),c),enc(b,0)))
    else:
        vectors=((enc(x,vote),enc(a,0)),(enc(y,1-vote),enc(b,0)))
    cache=copy.deepcopy(initial) if mutation!='drop_cache' else {}
    bad=initial_bad if mutation!='reset_flag' else False
    requests=[]; board=[]; decisions=[]; all_ballots=[]
    for voter,cts in enumerate(vectors):
        targets=cts+(mul(*cts),)
        proofs=[]
        for j,ct in enumerate(targets):
            stmt=enc(0,0) if j==2 and mutation=='dummy_aggregate' else ct
            p,c=transcript(stmt,coins[3*voter+j]); proofs.append(p)
            k=key(stmt,p)
            if not(j==2 and mutation=='skip_aggregate'):
                bad |= k in cache
                cache.setdefault(k,c)
                requests.insert(0,stmt)
        ballot=(cts,tuple(proofs)); all_ballots.append(ballot)
        verified=True
        for ct,p in zip(targets,proofs):
            # A deterministic fresh answer supplies a fixed raw oracle tape.
            c=cache.setdefault(key(ct,p),7)
            if not valid(ct,p,c):
                verified=False;break
        if mutation=='second_empty_board' and voter==1:
            board=[]
        fresh=all(t not in old[1] for t in targets for old in board)
        decision='invalidProof' if not verified else ('accepted' if fresh else 'reusedCiphertext')
        if mutation=='force_accept': decision='accepted'
        if decision=='accepted' or mutation=='append_rejected': board.append((voter,targets,ballot))
        decisions.append(decision)
    return tuple(decisions),board,cache,bad,requests,all_ballots

mutations=('dummy_aggregate','skip_aggregate','second_empty_board','force_accept',
           'append_rejected','drop_cache','reset_flag')
found=set();counts=dict(accepted=0,invalidProof=0,reusedCiphertext=0);cases=0
for seed in (17,41,103):
    rng=random.Random(seed)
    for trial in range(100):
        nonces=tuple(rng.randrange(1,Q) for _ in range(4));vote=trial % 2
        coins=[tuple(rng.randrange(Q) for _ in range(4)) for _ in range(6)]
        ct=enc(nonces[0],vote);proof,c=transcript(ct,coins[0])
        for mode in ('miss','agree','conflict'):
            initial={('foreign',0):5}
            if mode!='miss': initial[key(ct,proof)]=(c+(mode=='conflict')) % Q
            for bad in (False,True):
                reference=execute(vote,nonces,coins,initial,bad)
                actual=execute(vote,nonces,coins,initial,bad,challenge=True)
                assert actual==reference
                assert actual[2][('foreign',0)]==5 and (not bad or actual[3])
                assert len(actual[4])==6
                for d in actual[0]: counts[d]+=1
                for mutation in mutations:
                    if execute(vote,nonces,coins,initial,bad,True,mutation)!=reference:
                        found.add(mutation)
                cases+=1
assert all(counts.values()) and found==set(mutations)
# Complete public continuation fixtures for the random-mask enquiry. Replay or
# corrupt Alice's ballot, query the same live oracle adaptively, publish actual
# retained-board decryption and a simulated trustee proof, then guess from view.
# Fixed tapes enumerate mask distributions; they do not sample the full protocol.
def answer(cache,k):
    return cache.setdefault(k,int.from_bytes(hashlib.sha256(repr(k).encode()).digest()[:4],'big') % Q)

def finish(trace,aux,tape,corrupt):
    decisions,board,cache,bad,requests,ballots=copy.deepcopy(trace)
    aux=copy.deepcopy(aux)
    submission=ballots[0]
    cts,proofs=submission
    if corrupt:
        rows=[list(p) for p in proofs]
        a,b,d,z=rows[0][0];rows[0][0]=(a,b,d,(z+1)%Q)
        submission=(cts,tuple(tuple(p) for p in rows))
    saved=answer(cache,key(submission[0][0],submission[1][0]))
    targets=submission[0]+(mul(*submission[0]),)
    verified=all(valid(ct,p,answer(cache,key(ct,p))) for ct,p in zip(targets,submission[1]))
    fresh=all(t not in old[1] for t in targets for old in board)
    decision='invalidProof' if not verified else ('accepted' if fresh else 'reusedCiphertext')
    if decision=='accepted':board.append((2,targets,submission))
    tally=tuple(__import__('functools').reduce(mul,(row[1][i] for row in board),(1,1)) for i in range(2))
    shares=tuple(pow(ct[0],3,P) for ct in tally)
    trustees=[]
    for ct,share,(c,z) in zip(tally,shares,tape):
        commitment=(pow(G,z,P)*pow(pow(PK,c,P),-1,P)%P,
                    pow(ct[0],z,P)*pow(pow(share,c,P),-1,P)%P)
        aux.setdefault(('trustee',ct,share,commitment),c)
        trustees.append((commitment,c,z))
    plain=tuple(ct[1]*pow(share,-1,P)%P for ct,share in zip(tally,shares))
    view=(decisions,trace[1],submission,decision,board,tally,shares,tuple(trustees),plain)
    # Saved state and a post-publication oracle answer both influence guessing.
    after=answer(aux,('key',G,PK,(saved+sum(shares))%P))
    guess=(saved+after+sum(plain))%2
    return repr((view,cache,aux,bad,requests)),guess

full_mask_cases=0;full_decisions=set();fixed_mask_detected=False
for seed in (17,41,103):
    rng=random.Random(seed)
    for trial in range(20):
        x,t,a,b=(rng.randrange(Q) for _ in range(4))
        coins=[tuple(rng.randrange(Q) for _ in range(4)) for _ in range(6)]
        trustee_coins=[(rng.randrange(Q),rng.randrange(Q)) for _ in range(2)]
        initial={('foreign',0):5}
        if trial%3:
            p,c=transcript(enc(1,0),coins[0]);initial[key(enc(1,0),p)]=(c+trial%2)%Q
        aux={('key',G,PK,1):4}
        worlds=[Counter(),Counter()]
        for z in range(Q):
            outputs=[]
            for vote in (0,1):
                mask=(z-vote)%Q
                first=(pow(G,x,P),pow(G,mask+vote,P))
                vectors=((first,enc(a,0)),(div(enc(t,1),first),enc(b,0)))
                trace=execute(vote,(x,a,0,b),coins,initial,False,vectors=vectors)
                full_decisions.update(trace[0])
                out=finish(trace,aux,trustee_coins,trial%2==1)
                outputs.append(out);worlds[vote][out]+=1
                # With fixed z=0, a published Alice ciphertext leaks the bit.
                if mask==0 and trace[0][0]=='accepted':
                    assert trace[1][0][2][0][0][1]==pow(G,vote,P)
                    fixed_mask_detected=True
            assert outputs[0]==outputs[1]
            full_mask_cases+=1
        assert worlds[0]==worlds[1]
        wins=sum(n for (_,guess),n in worlds[0].items() if guess==0)+sum(n for (_,guess),n in worlds[1].items() if guess==1)
        assert wins==Q  # exactly half of 2Q executions, including rejections
assert fixed_mask_detected
assert 'accepted' in full_decisions and 'reusedCiphertext' in full_decisions
print(json.dumps(dict(seeds=[17,41,103],cases=cases,decision_counts=counts,
    detected_mutants=sorted(found),full_mask_cases=full_mask_cases,
    full_mask_honest_decisions=sorted(full_decisions),fixed_mask_leaks_vote=fixed_mask_detected,
    failures=0,gaveUp=0),indent=2))
