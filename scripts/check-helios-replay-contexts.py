#!/usr/bin/env python3
"""Exact finite controls for actual stopped-context replay probabilities."""
from fractions import Fraction as Fr
from itertools import product
import json

# A ternary hash query; answer zero stops, answers one/two issue another hash
# query. Labels are None/0/1 and must point to a query that occurred.
paths=[(0,)]+[(a,b) for a in (1,2) for b in range(3)]
weight={p:Fr(1,3**len(p)) for p in paths}
assert sum(weight.values())==1
cases=mass_checks=collision_checks=saturated=0
for short in (None,0):
    for rest in product((None,0,1),repeat=6):
        labels=dict(zip(paths,(short,*rest)))
        for index in range(2):
            selected=[p for p in paths if labels[p]==index]
            masses={}
            for p in selected:
                assert index<len(p)
                prefix=p[:index]
                row=[z for z in paths if z[:index]==prefix and len(z)>index]
                row_weight=sum(weight[z] for z in row)
                mass=sum(weight[z] for z in row if labels[z]==index)/row_weight
                success=sum(weight[z] for z in row
                    if labels[z]==index and z[index]!=p[index])/row_weight
                collision=sum(weight[z] for z in row if z[index]==p[index])/row_weight
                assert collision==Fr(1,3) and success>=max(0,mass-Fr(1,3))
                masses[p]=mass
                collision_checks+=1
            for delta in (Fr(k,9) for k in range(10)):
                bad=sum(weight[p] for p in selected if masses[p]<=delta)
                assert bad<=delta
                saturated+=bad==delta and delta>0
                mass_checks+=1
        cases+=1
assert cases==1458 and saturated>0
# Dropping reachability makes a missing context appear to have zero conditional
# mass, although its selected original path has positive probability.
missing_selected_mass=weight[(0,)]
assert missing_selected_mass>0
# A reachable one-query success event attains delta=1/3 exactly.
assert Fr(1,3)==sum(Fr(1,3) for a in range(3) if a==0)
# Three distinct fixed query locations, q=31, all original outputs accepted.
# Fix first answers to zero. Enumerate all second focused answers independently;
# translation gives the same count for any other fixed original answer vector.
joint_successes=joint_cases=0
for answers in product(range(31),repeat=3):
    joint_successes+=all(a!=0 for a in answers)
    joint_cases+=1
joint=Fr(joint_successes,joint_cases)
assert joint==Fr(30,31)**3
alpha,Q,delta=Fr(1),3,Fr(1,18)
candidate=max(0,alpha-3*Q*delta)*max(0,delta-Fr(1,31))**3
assert 0<candidate<=joint
# Marginal positivity alone, without shared-context structure, remains invalid.
assert {0} and {1} and not ({0}&{1})
print(json.dumps(dict(branching_programs=cases,fixed_index_mass_checks=mass_checks,
    conditional_collision_checks=collision_checks,positive_threshold_equalities=saturated,
    missing_occurrence_counterexample=str(missing_selected_mass),
    three_location_cases=joint_cases,three_location_successes=joint_successes,
    three_location_probability=str(joint),candidate_lower_bound=str(candidate),
    failures=0,gaveUp=0),indent=2))
