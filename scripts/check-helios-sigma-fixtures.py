#!/usr/bin/env python3
"""Independent multiplicative disjunctive-proof extraction fixtures."""
import json
from itertools import product
P, Q, G, PK = 23, 11, 2, 8

def enc(r,m):
    return pow(G,r,P), pow(G,m,P)*pow(PK,r,P)%P

def transcript(v,r,c,w=4,e=2,z=3):
    a,b=enc(r,v)
    fake=1-v
    fake_pair=(pow(G,z,P)*pow(pow(a,e,P),-1,P)%P,
               pow(PK,z,P)*pow(pow(b*pow(pow(G,fake,P),-1,P)%P,e,P),-1,P)%P)
    real_pair=(pow(G,w,P),pow(PK,w,P))
    cr=(c-e)%Q
    zr=(w+r*cr)%Q
    return ((fake_pair,real_pair),(e,z,zr)) if v else ((real_pair,fake_pair),(cr,zr,z))

def verify(ct,pc,c,resp):
    c0,z0,z1=resp
    for m, ((a,b),ch,z) in enumerate(zip(pc,[c0,(c-c0)%Q],[z0,z1])):
        if pow(G,z,P)!=a*pow(ct[0],ch,P)%P: return False
        t=ct[1]*pow(pow(G,m,P),-1,P)%P
        if pow(PK,z,P)!=b*pow(t,ch,P)%P: return False
    return True

def extract(c,p,d,q):
    if p[0]!=q[0]: return 0,(p[1]-q[1])*pow((p[0]-q[0])%Q,-1,Q)%Q
    denominator=(c-p[0]-d+q[0])%Q
    return 1,0 if denominator==0 else (p[2]-q[2])*pow(denominator,-1,Q)%Q

cases=source_tag_cases=wrong_second_tags=0
for v,r,c,d in product(range(2),range(Q),range(Q),range(Q)):
    if c==d: continue
    pc,p=transcript(v,r,c)
    qc,q=transcript(v,r,d)
    assert pc==qc
    assert verify(enc(r,v),pc,c,p) and verify(enc(r,v),qc,d,q)
    v_out,r_out=extract(c,p,d,q)
    assert (v_out,r_out)==(v,r)
    assert enc(r_out,v_out)==enc(r,v)
    # The source leaf contains a challenge-dependent public tag and the
    # original full proof. A physical first/second replay path uses c/d.
    first_source=(c==5,enc(r,v),pc,(p[0],p[1],(c-p[0])%Q,p[2]))
    second_source=(d==5,enc(r,v),qc,(q[0],q[1],(d-q[0])%Q,q[2]))
    path_answers=(c,d)
    recovered_pc,recovered_resp=transcript(v,r,path_answers[0])
    recovered=(path_answers[0]==5,enc(r,v),recovered_pc,
        (recovered_resp[0],recovered_resp[1],
         (path_answers[0]-recovered_resp[0])%Q,recovered_resp[2]))
    assert recovered==first_source
    retained_result=(recovered,(v_out,r_out))
    assert retained_result[1]==extract(c,p,d,q)
    assert first_source[1:3]==second_source[1:3]
    wrong_second_tags+=first_source[0]!=second_source[0]
    source_tag_cases+=1
    cases+=1
assert cases==source_tag_cases==2420 and wrong_second_tags==440
pc,p=transcript(0,3,5)
assert p==(3,2,3)
assert extract(5,p,5,p)==(1,0) and enc(0,1)!=enc(3,0)
qc,q=transcript(0,3,6,w=5)
assert pc!=qc and verify(enc(3,0),qc,6,q)
assert extract(5,p,6,q)==(0,4) and enc(4,0)!=enc(3,0)
# A full proof carries both challenges. Reconstructing c1 before checking it
# would erase this actual malformed-proof rejection.
normalization_defects=0
for v,r,c in product(range(2),range(Q),range(Q)):
    pc,resp=transcript(v,r,c)
    c0,z0,z1=resp
    full=(c0,z0,(c-c0)%Q,z1)
    bad=(c0,z0,(full[2]+1)%Q,z1)
    def verify_full(proof):
        return (proof[0]+proof[2])%Q==c and verify(enc(r,v),pc,c,
            (proof[0],proof[1],proof[3]))
    assert verify_full(full) and not verify_full(bad)
    assert verify(enc(r,v),pc,c,(bad[0],bad[1],bad[3]))
    normalization_defects+=1
# Same log position does not determine a key across unrelated executions.
# Coordinates are multiplicative group values, independent of Lean's exponents.
first=(enc(3,0),transcript(0,3,5)[0])
second=(enc(4,1),transcript(1,4,5,w=3)[0])
assert second == ((16,4),((18,9),(8,6)))
assert first != second and [first].index(first)==[second].index(second)==0
# Complete the actual verifier query. Compare native lazy verification with
# the replay trace, for an empty history and every possible cached answer.
# Cached cases arise from a preceding actual query, so its miss is in the log.
completion_cases=omitted_verifier_defects=0
for v,r,proof_c,prior in product(range(2),range(Q),range(Q),[None,*range(Q)]):
    ct=enc(r,v)
    pc,resp=transcript(v,r,proof_c)
    target=(ct,pc)
    initial={} if prior is None else {target:prior}
    log=[] if prior is None else [target]
    n=len(log)
    for fresh_c in (range(Q) if prior is None else [0]):
        native_cache=dict(initial)
        actual_c=native_cache.setdefault(target,fresh_c)
        accepted=verify(ct,pc,actual_c,resp) and actual_c==proof_c
        trace_cache=dict(initial)
        completed_log=list(log)
        if target not in trace_cache:
            trace_cache[target]=fresh_c
            completed_log.append(target)
        trace_accepted=verify(ct,pc,trace_cache[target],resp) and trace_cache[target]==proof_c
        selected=trace_accepted and target in completed_log and completed_log.index(target)<n+1
        assert selected==accepted and native_cache==trace_cache
        assert len(completed_log)<=n+1
        if prior is None and accepted:
            assert not (target in log)
            omitted_verifier_defects+=1
        completion_cases+=1
assert completion_cases==5324 and omitted_verifier_defects==242
# Joint-witness output contract, derived independently from multiplicative
# ciphertext equality. This does not search for, or measure, a replay extractor.
joint_cases=joint_witnesses=double_vote_defects=0
joint_counts=[0,0,0]
for b0,b1,r0,r1 in product(range(2),range(2),range(Q),range(Q)):
    ct0,ct1=enc(r0,b0),enc(r1,b1)
    aggregate=tuple(a*b%P for a,b in zip(ct0,ct1))
    found=[]
    for ba,ra in product(range(2),range(Q)):
        joint_cases+=1
        if aggregate==enc(ra,ba):
            assert ra==(r0+r1)%Q and ba==b0+b1 and b0+b1<=1
            found.append((ba,ra))
            joint_witnesses+=1
    assert len(found)==(1 if b0+b1<=1 else 0)
    joint_counts[b0+b1]+=1
    if b0+b1==2:
        # Components alone both prove a bit; omitting the aggregate constraint
        # would accept this integer count of two.
        assert not found
        double_vote_defects+=1
assert (joint_cases,joint_witnesses,double_vote_defects)==(10648,363,121)
assert joint_counts==[121,242,121]
# Independent additive four-element-field coordinate model: addition is XOR
# in F_2[x]/(x^2+x+1). At g=pk=1, Enc(r,m)=(r,m+r).
# Cardinality is four, but two component ones still sum to the aggregate zero.
char_two_wrapped=0
for r0,r1 in product(range(4),repeat=2):
    ct0,ct1=(r0,1^r0),(r1,1^r1)
    aggregate=(ct0[0]^ct1[0],ct0[1]^ct1[1])
    assert aggregate==(r0^r1,0^(r0^r1)) and 1+1>1
    char_two_wrapped+=1
assert char_two_wrapped==16
# Shared original three-proof replay, at three distinct actual hash targets.
# Enumerate all first challenge vectors; each replay either keeps its selected
# answer (must fail the fork) or changes it by one. The prefix before that query
# stays fixed. Subsequent answers use the original vector, a supported completion.
shared_cases=shared_successes=shared_failures=wrong_joint_sources=0
for b0,b1 in [(0,0),(1,0),(0,1)]:
    witnesses=[(b0,3),(b1,4),(b0+b1,7)]
    targets=[(enc(r,b),transcript(b,r,0)[0]) for b,r in witnesses]
    assert len(set(targets))==3
    for answers in product(range(Q),repeat=3):
        first_proofs=[transcript(b,r,c) for (b,r),c in zip(witnesses,answers)]
        first_source=(tuple(c==5 for c in answers),tuple(first_proofs))
        for changes in product(range(2),repeat=3):
            recovered=[]
            for i,change in enumerate(changes):
                second_answers=list(answers)
                second_answers[i]=(answers[i]+change)%Q
                assert tuple(second_answers[:i])==answers[:i]
                b,r=witnesses[i]
                pc,p=first_proofs[i]
                qc,q=transcript(b,r,second_answers[i])
                assert pc==qc and verify(enc(r,b),pc,answers[i],p)
                assert verify(enc(r,b),qc,second_answers[i],q)
                recovered.append(extract(answers[i],p,second_answers[i],q) if change else None)
                if change:
                    assert recovered[-1]==witnesses[i]
                    wrong_joint_sources+=tuple(c==5 for c in second_answers)!=first_source[0]
            joint=None if None in recovered else (first_source,tuple(recovered))
            if joint is None:
                shared_failures+=1
                assert not all(changes)
            else:
                shared_successes+=1
                assert all(changes) and joint[0]==first_source
                assert joint[1][2][1]==(joint[1][0][1]+joint[1][1][1])%Q
                assert joint[1][0][0]+joint[1][1][0]==joint[1][2][0]<=1
            shared_cases+=1
assert (shared_cases,shared_successes,shared_failures)==(31944,3993,27951)
assert wrong_joint_sources>0
# The first-path success sets of two marginals may be disjoint. This independently
# detects the invalid inference from positive marginals to positive joint success.
marginal_events=[{True},{False}]
assert all(marginal_events) and not set.intersection(*marginal_events)
print(json.dumps(dict(cases=cases, failures=0, gaveUp=0,
    shared_replay_cases=shared_cases, shared_replay_successes=shared_successes,
    shared_replay_failures=shared_failures, wrong_joint_sources_detected=wrong_joint_sources,
    disjoint_marginal_counterexamples=1,
    joint_witness_comparisons=joint_cases, consistent_joint_witnesses=joint_witnesses,
    omitted_aggregate_double_votes=double_vote_defects,
    characteristic_two_wrapped_cases=char_two_wrapped,
    retained_source_cases=source_tag_cases, wrong_second_tags_detected=wrong_second_tags,
    normalization_defects_detected=normalization_defects,
    verifier_completion_cases=completion_cases,
    omitted_verifier_defects_detected=omitted_verifier_defects,
    unrelated_same_index_targets=[first,second],
    same_challenge_invalid_witness=[1,0], changed_commitment_invalid_witness=[0,4]),indent=2))
