#!/usr/bin/env python3
"""Exact multiplicative proof/flag/cache distributions, independent of Lean."""
from collections import Counter
from fractions import Fraction
from itertools import product
import json

results=[]
for p,q,g in [(7,3,2),(11,5,3),(23,11,2)]:
    pk=pow(g,2,p)
    for v in (0,1):
        ct=(g,pow(g,v,p)*pk%p)  # nonce 1
        stmt=(g,pk,*ct)
        def branch(m,c,z):
            return (pow(g,z,p)*pow(pow(ct[0],c,p),-1,p)%p,
                    pow(pk,z,p)*pow(pow(ct[1]*pow(pow(g,m,p),-1,p)%p,c,p),-1,p)%p)
        def sim(c,e,z0,z1):
            return (branch(0,e,z0),branch(1,(c-e)%q,z1)),c,(e,z0,z1)
        def real(w,e,z,c):
            honest=(pow(g,w,p),pow(pk,w,p))
            fake=branch(1-v,e,z)
            cr=(c-e)%q
            zr=(w+cr)%q
            return ((fake,honest),c,(e,z,zr)) if v else ((honest,fake),c,(cr,zr,z))
        transcripts=[sim(*coins) for coins in product(range(q),repeat=4)]
        keys={(stmt,pc) for pc,_,_ in transcripts}
        zero_key=(stmt,((1,1),(1,1)))
        assert zero_key in keys
        for regime,cache in [('empty',{}),('single',{zero_key:1}),
                ('full',{key:1 for key in keys}),
                ('unrelated',{((g,pk,ct[0],ct[1]*g%p),zero_key[1]):1})]:
            simulated=Counter()
            real_full=Counter()
            real_actual=Counter()
            # Final cache is represented by a delta from the shared fixed cache.
            # Existing entries are unchanged in every branch.
            for pc,c,resp in transcripts:
                key=(stmt,pc)
                hit=key in cache
                delta=None if hit else (key,c)
                simulated[pc,c,resp,hit,delta]+=1
            for w,e,z,dummy in product(range(q),repeat=4):
                pc,_,_=real(w,e,z,dummy)
                key=(stmt,pc)
                c=cache.get(key,dummy)
                _,_,resp=real(w,e,z,c)
                delta=None if key in cache else (key,c)
                out=(pc,c,resp,False,delta)
                real_full[out]+=1
                if w and e and z:
                    real_actual[out]+=1
            def tv(a,b):
                na,nb=sum(a.values()),sum(b.values())
                return sum(abs(Fraction(a[x],na)-Fraction(b[x],nb)) for x in a.keys()|b.keys())/2
            distance=tv(real_actual,simulated)
            full_distance=tv(real_full,simulated)
            bad=Fraction(sum(n for (_,_,_,flag,_),n in simulated.items() if flag),q**4)
            bound=Fraction(3+len(cache),q)
            assert full_distance==bad
            assert distance<=bound
            if regime=='empty':
                assert distance>0  # deleting the historical sampling loss is false
            if regime=='full':
                assert full_distance==1  # deleting the collision term is false
                if q>3:
                    assert distance>Fraction(3,q)
            results.append(dict(q=q,vote=v,cache=regime,entries=len(cache),
                actual_draws=sum(real_actual.values()),full_draws=q**4,
                distance=str(distance),full_distance=str(full_distance),bad=str(bad),bound=str(bound)))
print(json.dumps(dict(results=results,failures=0,gaveUp=0),indent=2))
