#!/usr/bin/env python3
"""Independent native tape/event fixtures; no source compiler is tested here."""
import copy
import json
import random


def word(tape):
    cells,head=tape
    out=[]
    while cells.get(head) is not None:
        out.append(cells[head]);head+=1
    return out


def event(state,kind,reply,mutant=None):
    work,query,answer=copy.deepcopy(state)
    request=('hash',tuple(word(query))) if kind=='hash' else ('coin',)
    answer=({i:b for i,b in enumerate(reply)},0)
    if mutant=='work_alias':work=copy.deepcopy(answer)
    if mutant=='query_reset':query=({},0)
    return (work,query,answer),request

cases=0
for seed in [7,19,41]:
    rng=random.Random(seed)
    for _ in range(1000):
        state=tuple(({i:rng.choice([None,False,True]) for i in range(-4,5)},rng.randrange(-3,4)) for _ in range(3))
        kind=rng.choice(['hash','coin'])
        reply=[bool(rng.randrange(2)) for _ in range(rng.randrange(13) if kind=='hash' else 1)]
        before=copy.deepcopy(state)
        after,request=event(state,kind,reply)
        assert state==before and after[:2]==before[:2]
        assert after[2][1]==0 and word(after[2])==reply
        assert all(after[2][0].get(i) is None for i in range(-12,0))
        expected=[]
        cells,head=before[1]
        for i in range(head,6):
            if cells.get(i) is None:break
            expected.append(cells[i])
        assert request==(('hash',tuple(expected)) if kind=='hash' else ('coin',))
        cases+=1
fixture=(({ -1:True,0:False,1:True},0),({-1:True,0:False,2:True},0),({0:True,1:True},1))
assert event(fixture,'hash',[False,True])[1]==('hash',(False,))
for mutant in ['work_alias','query_reset']:
    assert event(fixture,'hash',[False,True],mutant)!=event(fixture,'hash',[False,True])
print(json.dumps(dict(cases=cases,seeds=[7,19,41],cell_positions=[-4,4],head_positions=[-3,3],hash_reply_lengths=[0,12],failures=0,gaveUp=0,mutants=['work_alias','query_reset'],scope='Native events only; source compilation not tested'),indent=2))
