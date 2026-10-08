#!/usr/bin/env python3
"""Independent multiplicative strong-proof and shared-cache fixtures (p=23,q=11)."""
from itertools import product
import json

p,q,g,pk=23,11,2,8

def enc(r,v):
    return pow(g,r,p),pow(g,v,p)*pow(pk,r,p)%p

def branch(ct,m,e,z):
    return (pow(g,z,p)*pow(pow(ct[0],e,p),-1,p)%p,
            pow(pk,z,p)*pow(pow(ct[1]*pow(pow(g,m,p),-1,p)%p,e,p),-1,p)%p)

def key(ct,pc):
    return (g,pk,*ct,*pc[0],*pc[1])

def check(ct,pc,c0,c1,z0,z1,total):
    return (c0+c1)%q==total and pc[0]==branch(ct,0,c0,z0) and pc[1]==branch(ct,1,c1,z1)

cases=0
for v,r in product(range(2),range(q)):
    ct=enc(r,v)
    for w,e,z in product(range(1,q),repeat=3):
        real=(pow(g,w,p),pow(pk,w,p))
        fake=branch(ct,1-v,e,z)
        pc=(fake,real) if v else (real,fake)
        cache={}
        k=key(ct,pc)
        # A deterministic answer fixture; agreement must hold for every hash.
        answer=sum(k)%q
        cache[k]=answer
        cr=(answer-e)%q
        zr=(w+r*cr)%q
        c0,c1,z0,z1=(e,cr,z,zr) if v else (cr,e,zr,z)
        assert check(ct,pc,c0,c1,z0,z1,cache[k])
        # Resetting the cache can return a different challenge and reject.
        assert not check(ct,pc,c0,c1,z0,z1,(answer+1)%q)
        cases+=1

ct=enc(3,0)
c,e,z0,z1=5,2,3,4
pc=(branch(ct,0,e,z0),branch(ct,1,(c-e)%q,z1))
k=key(ct,pc)
cache={}
cache[k]=c
assert check(ct,pc,e,(c-e)%q,z0,z1,cache[k])
# Each of the eight hashed group coordinates affects query identity.
for i in range(len(k)):
    altered=list(k)
    altered[i]=altered[i]*g%p
    altered=tuple(altered)
    assert altered!=k and altered not in cache
    # The dropped-coordinate mutation identifies these distinct queries.
    assert altered[:i]+altered[i+1:]==k[:i]+k[i+1:]
# A conflicting pre-query must remain unchanged and be reported as bad.
prior={k:(c+1)%q}
snapshot=dict(prior)
bad=k in prior
if not bad:
    prior[k]=c
assert bad and prior==snapshot
assert not check(ct,pc,e,(c-e)%q,z0,z1,prior[k])
# Historical column-wise coins versus nonce-first, proof-wise requests.
# Exhaustive labelled nonzero draws over {1,2}; the permutation is bijective.
# These are distribution/permutation and constructor controls, not RO security.
def prove(ct,v,r,w,e,z):
    real=(pow(g,w,p),pow(pk,w,p))
    fake=branch(ct,1-v,e,z)
    pc=(fake,real) if v else (real,fake)
    c=sum(key(ct,pc))%q
    cr=(c-e)%q
    zr=(w+r*cr)%q
    cs,zs=((e,cr),(z,zr)) if v else ((cr,e),(zr,z))
    assert check(ct,pc,*cs,*zs,c)
    return pc,cs,zs

ballot_cases=permutation_cases=wrong_aggregate=wrong_transpose=0
images=set()
for coins in product((1,2),repeat=11):
    w,e,z=coins[:3],coins[3:6],coins[6:9]
    r,s=coins[9:]
    ordered=(r,s,w[0],e[0],z[0],w[1],e[1],z[1],w[2],e[2],z[2])
    images.add(ordered)
    permutation_cases+=1
    for vote in (0,1):
        cts=(enc(r,vote),enc(s,0),enc((r+s)%q,vote))
        assert cts[2]==(cts[0][0]*cts[1][0]%p,cts[0][1]*cts[1][1]%p)
        old=tuple(prove(ct,v,n,w[i],e[i],z[i])
                  for i,(ct,v,n) in enumerate(zip(cts,(vote,0,vote),(r,s,(r+s)%q))))
        nonce0,nonce1,*byproof=ordered
        actual=tuple(prove(ct,v,n,*byproof[3*i:3*i+3])
                     for i,(ct,v,n) in enumerate(zip(cts,(vote,0,vote),
                                                    (nonce0,nonce1,(nonce0+nonce1)%q))))
        assert old==actual
        wrong_aggregate+=enc(r,vote)!=cts[2]
        wrong_transpose+=old!=tuple(prove(ct,v,n,*coins[3*i:3*i+3])
                     for i,(ct,v,n) in enumerate(zip(cts,(vote,0,vote),(r,s,(r+s)%q))))
        ballot_cases+=1
assert len(images)==permutation_cases==2048
assert wrong_aggregate==ballot_cases==4096 and wrong_transpose>0
# Supported nonzero summands can still produce an identity aggregate.
zero_aggregate=enc((1+10)%q,0)
assert zero_aggregate==(1,1)
prove(zero_aggregate,0,0,1,2,2)
# Submission decision and short-circuit verification, using actual full proofs.
decision_cases=priority_defects=aggregate_defects=0
for valid_bits,fresh in product(product((False,True),repeat=3),(False,True)):
    altered=[]
    for wanted,(pc,cs,zs) in zip(valid_bits,actual):
        altered.append((pc,cs if wanted else (cs[0],(cs[1]+1)%q),zs))
    reads=[]
    all_valid=True
    for j,(ct,(pc,cs,zs)) in enumerate(zip(cts,altered)):
        reads.append(key(ct,pc))
        if not check(ct,pc,*cs,*zs,sum(key(ct,pc))%q):
            all_valid=False
            break
    assert all_valid==all(valid_bits)
    decision='invalidProof' if not all_valid else ('accepted' if fresh else 'reusedCiphertext')
    expected='accepted' if all(valid_bits) and fresh else ('reusedCiphertext' if all(valid_bits) else 'invalidProof')
    assert decision==expected
    assert len(reads)==(next((j+1 for j,v in enumerate(valid_bits) if not v),3))
    if not fresh and not all_valid:
        assert decision!='reusedCiphertext'
        priority_defects+=1
    if valid_bits==(True,True,False):
        assert decision=='invalidProof'
        aggregate_defects+=1
    decision_cases+=1
assert decision_cases==16 and priority_defects==7 and aggregate_defects==2
# Actual two-honest-prefix executions with one shared lazy cache. Exhaust all
# nonzero encryption nonce pairs in both worlds and two answer policies; fixed
# nonzero proof coins are a fixture, not exhaustive proof-randomness coverage.
def lazy_ballot(v,r,s,cache,offset):
    cts=(enc(r,v),enc(s,0),enc((r+s)%q,v))
    proofs=[]
    for ct,bit,nonce in zip(cts,(v,0,v),(r,s,(r+s)%q)):
        w,e,z=4,2,3
        real=(pow(g,w,p),pow(pk,w,p))
        fake=branch(ct,1-bit,e,z)
        pc=(fake,real) if bit else (real,fake)
        target=key(ct,pc)
        challenge=cache.setdefault(target,(sum(target)+offset)%q)
        cr=(challenge-e)%q
        zr=(w+nonce*cr)%q
        cs,zs=((e,cr),(z,zr)) if bit else ((cr,e),(zr,z))
        proofs.append((pc,cs,zs))
    return cts,proofs

def honest_submit(ballot,board,cache):
    cts,proofs=ballot
    before=dict(cache)
    for ct,(pc,cs,zs) in zip(cts,proofs):
        assert key(ct,pc) in cache
        assert check(ct,pc,*cs,*zs,cache[key(ct,pc)])
    assert cache==before
    if any(ct in old for ct in cts for old in board):
        return 'reusedCiphertext',board
    return 'accepted',board+[cts]

prefix_cases=prefix_rejected=aggregate_zero_prefixes=0
for offset,v,r,s,t,u in product(range(2),range(2),range(1,q),range(1,q),range(1,q),range(1,q)):
    shared={}
    alice=lazy_ballot(v,r,s,shared,offset)
    d0,board=honest_submit(alice,[],shared)
    assert d0=='accepted'
    bob=lazy_ballot(1-v,t,u,shared,offset)
    d1,final=honest_submit(bob,board,shared)
    collision=not set((r,s,(r+s)%q)).isdisjoint((t,u,(t+u)%q))
    if d1!='accepted':
        assert collision and final==board
        prefix_rejected+=1
    else:
        assert final==[alice[0],bob[0]]
    aggregate_zero_prefixes+=((r+s)%q==0 or (t+u)%q==0)
    prefix_cases+=1
assert prefix_cases==40000 and prefix_rejected==11200
assert prefix_rejected/prefix_cases<=9/(q-1) and aggregate_zero_prefixes>0
# A zero additive generator is multiplicative identity here: all ciphertexts
# coincide and Bob is always rejected. This refutes dropping injectivity.
old_g,old_pk=g,pk
g=pk=1
zero_generator_cases=0
for v,r,s,t,u in product(range(2),(1,2),(1,2),(1,2),(1,2)):
    shared={}
    _,board=honest_submit(lazy_ballot(v,r,s,shared,0),[],shared)
    decision,final=honest_submit(lazy_ballot(1-v,t,u,shared,0),board,shared)
    assert decision=='reusedCiphertext' and final==board
    zero_generator_cases+=1
g,pk=old_g,old_pk
# Programmed honest prefixes followed by a raw three-proof attacker. The
# attacker reuses one shared shadow/live oracle and casts a fixed fresh-candidate
# ballot. The replay selector keeps its original full proof only on the joint
# honest/attacker acceptance event. Fixed simulator coins are fixture scope.
def programmed_ballot(v,r,s,shadow,recorded):
    cts=(enc(r,v),enc(s,0),enc((r+s)%q,v))
    proofs=[]
    for ct in cts:
        c,e,z0,z1=5,2,3,4
        pc=(branch(ct,0,e,z0),branch(ct,1,(c-e)%q,z1))
        shadow.setdefault(key(ct,pc),c)
        recorded.append(ct)
        proofs.append((pc,(e,(c-e)%q),(z0,z1)))
    return cts,proofs

def raw_prove_on_programmed(v,r,s,shadow,live):
    cts=(enc(r,v),enc(s,0),enc((r+s)%q,v))
    proofs=[]
    for ct,bit,nonce in zip(cts,(v,0,v),(r,s,(r+s)%q)):
        w,e,z=4,2,3
        real=(pow(g,w,p),pow(pk,w,p))
        fake=branch(ct,1-bit,e,z)
        pc=(fake,real) if bit else (real,fake)
        target=key(ct,pc)
        if target not in shadow:
            shadow[target]=live.setdefault(target,sum(target)%q)
        c=shadow[target]
        cr=(c-e)%q
        zr=(w+nonce*cr)%q
        cs,zs=((e,cr),(z,zr)) if bit else ((cr,e),(zr,z))
        proofs.append((pc,cs,zs))
    return cts,proofs

composed_cases=composed_accepted=excluded_valid_fallbacks=0
coverage_cases=coverage_enabled=coverage_omitted_targets=0
for v,r,s,t,u in product(range(2),range(1,q),range(1,q),range(1,q),range(1,q)):
    shadow,live,recorded={},{},[]
    alice=programmed_ballot(v,r,s,shadow,recorded)
    d0,board=honest_submit(alice,[],shadow)
    bob=programmed_ballot(1-v,t,u,shadow,recorded)
    d1,board=honest_submit(bob,board,shadow)
    attacker=raw_prove_on_programmed(0,6,9,shadow,live)
    da,final=honest_submit(attacker,board,shadow)
    accepted=d0==d1==da=='accepted'
    if accepted:
        composed_accepted+=1
        assert all(ct not in recorded for ct in attacker[0])
        for ct,(pc,cs,zs) in zip(*attacker):
            assert key(ct,pc) in live
            assert shadow[key(ct,pc)]==live[key(ct,pc)]
            assert check(ct,pc,*cs,*zs,live[key(ct,pc)])
    elif da=='accepted':
        # A genuine accepted full proof is excluded because an honest ballot
        # was rejected. The extraction guard must not silently drop that event.
        assert d1=='reusedCiphertext'
        excluded_valid_fallbacks+=1
    # The invalid fallback fails for every possible hash challenge, independent
    # of the actual ciphertext. Its zero branch would require identity = g.
    if not accepted:
        pc=((g,1),(1,1))
        for ct in attacker[0]:
            assert all(not check(ct,pc,0,0,0,0,c) for c in range(q))
    # The insertion-ordered live cache records exactly the miss order in this
    # empty-start fixture. Coverage uses the full selected proof and the same
    # original source cache, without appending a verifier completion.
    miss_log=list(live)
    enabled=[]
    for ct,(pc,cs,zs) in zip(*attacker):
        if not accepted:
            pc,cs,zs=((g,1),(1,1)),(0,0),(0,0)
        target=key(ct,pc)
        valid=target in live and check(ct,pc,*cs,*zs,live[target])
        selected=(miss_log.index(target) if valid and target in miss_log else None)
        assert (selected is not None)==accepted
        if selected is not None:
            assert selected<3+15+1 and miss_log[selected]==target
            assert live[miss_log[selected]]==shadow[target]
            omitted=[x for x in miss_log if x!=target]
            assert target not in omitted
            coverage_enabled+=1
            coverage_omitted_targets+=1
        enabled.append(selected is not None)
        coverage_cases+=1
    assert all(enabled)==accepted and len(miss_log)<=3
    composed_cases+=1
assert coverage_cases==60000 and coverage_enabled==coverage_omitted_targets==8160
assert composed_cases==20000 and composed_accepted>0 and excluded_valid_fallbacks>0
print(json.dumps(dict(constructor_cases=cases,reset_cache_defects_detected=cases,
    hash_coordinates_checked=len(k),fresh_simulation_valid=True,
    ballot_cases=ballot_cases,coin_permutations=permutation_cases,
    zero_aggregate_ciphertext=zero_aggregate,
    submission_decision_cases=decision_cases,priority_defects=priority_defects,
    omitted_aggregate_defects=aggregate_defects,
    wrong_aggregate_defects=wrong_aggregate,wrong_transpose_defects=wrong_transpose,
    prefix_cases=prefix_cases,prefix_rejected=prefix_rejected,
    aggregate_zero_prefixes=aggregate_zero_prefixes,zero_generator_cases=zero_generator_cases,
    selector_coverage_cases=coverage_cases,selectors_enabled=coverage_enabled,
    omitted_miss_targets_detected=coverage_omitted_targets,
    composed_cases=composed_cases,composed_accepted=composed_accepted,
    excluded_valid_fallbacks=excluded_valid_fallbacks,
    conflicting_cache_preserved=True,failures=0,gaveUp=0),indent=2))
