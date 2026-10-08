#!/usr/bin/env python3
"""Exact finite distributions from independently coded multiplicative transcripts."""
import json
from collections import Counter
from fractions import Fraction
from itertools import product

results=[]
for p,q,g in [(7,3,2),(11,5,3),(23,11,2)]:
    pk=pow(g,2,p)
    for vote in [0,1]:
        nonce=1
        ct=(pow(g,nonce,p),pow(g,vote,p)*pow(pk,nonce,p)%p)
        def sim_branch(m,c,z):
            return (pow(g,z,p)*pow(pow(ct[0],c,p),-1,p)%p,
                pow(pk,z,p)*pow(pow(ct[1]*pow(pow(g,m,p),-1,p)%p,c,p),-1,p)%p)
        def real(w,e,z,c):
            fake=sim_branch(1-vote,e,z)
            genuine=(pow(g,w,p),pow(pk,w,p))
            cr=(c-e)%q
            zr=(w+nonce*cr)%q
            pc=(fake,genuine) if vote else (genuine,fake)
            resp=(e,z,zr) if vote else (cr,zr,z)
            return pc,c,resp
        def sim(c,e,z0,z1):
            return (sim_branch(0,e,z0),sim_branch(1,(c-e)%q,z1)),c,(e,z0,z1)
        full=Counter(real(w,e,z,c) for w,e,z,c in product(range(q),repeat=4))
        simulated=Counter(sim(c,e,z0,z1) for c,e,z0,z1 in product(range(q),repeat=4))
        actual=Counter(real(w,e,z,c) for w,e,z in product(range(1,q),repeat=3) for c in range(q))
        assert full==simulated
        marginal=Counter()
        joint=Counter()
        for (commit,challenge,_),count in simulated.items():
            marginal[commit]+=count
            joint[commit,challenge]+=count
        assert max(marginal.values()) <= q**3
        assert all(joint[commit,c]*q==count for commit,count in marginal.items() for c in range(q))
        actual_size=(q-1)**3*q
        full_size=q**4
        tv=sum(abs(Fraction(actual[t],actual_size)-Fraction(simulated[t],full_size))
               for t in full.keys() | actual.keys())/2
        assert tv == 1-Fraction((q-1)**3,q**3)
        assert 0<tv<=Fraction(3,q)
        if vote==0:
            assert not any((c-resp[0])%q==0 for _,c,resp in actual)
            zero_count=sum(n for (_,c,resp),n in simulated.items() if (c-resp[0])%q==0)
            assert Fraction(zero_count,full_size)==Fraction(1,q)
        results.append(dict(p=p,q=q,vote=vote,actual_draws=actual_size,full_draws=full_size,
            simulator_draws=full_size,tv=str(tv),bound=str(Fraction(3,q))))
# Removing generator injectivity makes the commitment constant.
p,q,g=7,3,1
pk=1
ct=(1,1)
degenerate=Counter(sim(c,e,z0,z1)[0] for c,e,z0,z1 in product(range(q),repeat=4))
assert degenerate==Counter({((1,1),(1,1)):q**4})
# An encryption of 2 has no bit witness; conditioning on zero commitments
# forces total challenge zero, refuting witness-free conditional uniformity.
p,q,g=7,3,2
pk=pow(g,2,p)
ct=(g,pow(g,2,p)*pk%p)
invalid=Counter(sim(c,e,z0,z1) for c,e,z0,z1 in product(range(q),repeat=4))
zero_commit=((1,1),(1,1))
zero_events=[(c,n) for (pc,c,_),n in invalid.items() if pc==zero_commit]
assert zero_events==[(0,1)]
print(json.dumps(dict(results=results,degenerate_commit_probability="1",
    invalid_zero_commit_challenges=zero_events,failures=0,gaveUp=0),indent=2))
