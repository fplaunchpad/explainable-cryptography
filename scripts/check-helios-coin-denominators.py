#!/usr/bin/env python3
"""Independent exact rational fixtures for finite fair-coin trees."""
from fractions import Fraction
from collections import Counter
import json

words = [(a,b) for a in [0,1] for b in [0,1]]
modulo = Counter((2*a+b)%3 for a,b in words)
assert [Fraction(modulo[i],4) for i in range(3)] == [Fraction(1,2),Fraction(1,4),Fraction(1,4)]
assert len(set(modulo.values())) != 1
reject = Counter(2*a+b if 2*a+b<3 else None for a,b in words)
assert all(Fraction(reject[i],4)==Fraction(1,4) for i in [0,1,2,None])
# Retrying only up to a fixed cutoff preserves a nonzero failure mass.
for k in range(1,9):
    fail=Fraction(1,4)**k
    point=sum(Fraction(1,4)**j for j in range(1,k+1))
    assert fail>0 and 3*point+fail==1 and point != Fraction(1,3)
# Enumerate distinct outcome masses of all binary trees through depth 4.
masses={Fraction(0),Fraction(1)}
counts=[]
for depth in range(5):
    assert all((p*2**depth).denominator==1 for p in masses)
    assert Fraction(1,3) not in masses
    counts.append(len(masses))
    masses |= {(a+b)/2 for a in masses for b in masses}
# Positive controls: one coin and two coins sample 2 and 4 outcomes uniformly.
assert Counter(a for a in [0,1])=={0:1,1:1}
assert Counter(2*a+b for a,b in words)=={0:1,1:1,2:1,3:1}
print(json.dumps(dict(distinct_masses_by_depth=counts,modulo_masses=['1/2','1/4','1/4'],
    cutoff_depths=8,detected_mutations=['uniform_modulo_claim','zero_cutoff_failure'],
    failures=0,gaveUp=0),indent=2))
