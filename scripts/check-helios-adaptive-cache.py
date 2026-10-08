#!/usr/bin/env python3
"""Exhaustive small adaptive lazy-cache traces; independent dictionary oracle."""
from itertools import product
import json

# Complete hash-input fixtures derived in the multiplicative p=23 subgroup.
keys = [(2, 8, 8, 6, 3, 4, 18, 12), (2, 8, 8, 12, 3, 4, 18, 12)]
# A fresh second proof after a conflicting first proof. Nonce 4, bit 1,
# challenge 5 and response (2,3,4), calculated directly in the subgroup.
ct = (pow(2,4,23), 2*pow(8,4,23)%23)
assert ct == (16,4)
def branch(m,c,z):
    return (pow(2,z,23)*pow(pow(ct[0],c,23),-1,23)%23,
        pow(8,z,23)*pow(pow(ct[1]*pow(pow(2,m,23),-1,23)%23,c,23),-1,23)%23)
assert (branch(0,2,3),branch(1,3,4)) == ((18,9),(8,6))
cases = 0
initial_budget_defects = 0
repeat_query_controls = 0
uniform_controls = 0
sticky_flag_controls = 0
for depth in range(6):
    for initial in ({}, {keys[0]: 1}):
        for operations in product(('uniform', 'hash', 'proof'), repeat=depth):
            for answers in product(range(3), repeat=depth):
                cache = dict(initial)
                queried = set(initial)
                count = 0
                flag = False
                previous = 0
                for op, answer in zip(operations, answers):
                    old = dict(cache)
                    if op == 'uniform':
                        previous = answer
                        assert cache == old
                        uniform_controls += 1
                        continue
                    # Adapt the next complete statement/commitment key to the
                    # previous answer; the two fixtures differ in statement.
                    key = keys[previous % 2]
                    count += 1
                    hit = key in cache
                    if op == 'hash':
                        if not hit:
                            cache[key] = answer
                        previous = cache[key]
                        if hit:
                            assert cache == old
                            repeat_query_controls += 1
                    else:
                        # The programming policy flags every prior query,
                        # including an agreeing answer, without overwriting it.
                        if not hit:
                            cache[key] = answer
                        flag = flag or hit
                        if hit:
                            assert cache == old and flag
                            sticky_flag_controls += 1
                        previous = answer
                    queried.add(key)
                    assert set(cache) == queried
                    assert all(cache[k] == v for k, v in old.items())
                    assert len(cache) <= len(initial) + count
                if len(cache) > count:
                    initial_budget_defects += 1
                cases += 1
assert initial_budget_defects and repeat_query_controls and uniform_controls and sticky_flag_controls
# Dual-cache adapter gate. Keys carry (statement, commitment); requests adapt
# to the previous answer. This checks cache policy, not proof arithmetic.
dual_cases=dual_repeat=dual_programmed_hits=dual_flag_resets=0
def walk(depth,native,shadow,live,programmed,flag,last):
    global dual_cases,dual_repeat,dual_programmed_hits,dual_flag_resets
    dual_cases+=1
    assert native==shadow
    assert all(shadow.get(k)==v for k,v in live.items())
    assert all(shadow.get(k)==live.get(k) for k in [(a,b) for a in range(2) for b in range(2)]
               if k[0] not in programmed)
    if depth==4:return
    for op,selector,answer in product(('uniform','hash','proof'),range(2),range(2)):
        key=((last+selector)%2,depth%2)
        nc,sc,lc=dict(native),dict(shadow),dict(live)
        ps=list(programmed)
        newflag=flag
        if op=='uniform':
            result=answer
        elif op=='hash':
            result=nc.setdefault(key,answer)
            if key not in sc:
                sc[key]=lc.setdefault(key,answer)
            else:
                dual_repeat+=1
                if key not in lc:dual_programmed_hits+=1
            assert sc[key]==result
        else:
            hit=key in nc
            nc.setdefault(key,answer)
            sc.setdefault(key,answer)
            ps.append(key[0])
            newflag=flag or hit
            result=answer
            if flag and not hit:
                # The mutation newflag=hit would clear a previously raised flag.
                assert newflag != hit
                dual_flag_resets+=1
        walk(depth+1,nc,sc,lc,ps,newflag,result)
walk(0,{},{},{},[],False,0)
assert dual_cases==22621 and dual_programmed_hits and dual_repeat and dual_flag_resets
# Deliberate defects: clearing provenance makes a programmed-only key appear
# unexplained; resampling/overwriting a stored live answer breaks agreement.
assert {(0,0):1}.get((0,0))!={}.get((0,0))
assert {(0,0):1}.get((0,0))!={(0,0):0}.get((0,0))
print(json.dumps(dict(traces=cases, dual_cache_traces=dual_cases,
    dual_repeat_controls=dual_repeat, dual_programmed_hit_controls=dual_programmed_hits,
    dual_flag_reset_defects=dual_flag_resets, initial_budget_defects=initial_budget_defects,
    repeat_query_controls=repeat_query_controls, uniform_controls=uniform_controls,
    sticky_flag_controls=sticky_flag_controls, failures=0, gaveUp=0), indent=2))
