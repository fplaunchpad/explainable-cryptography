#!/usr/bin/env python3
"""Check the two-pass raw-input converter against literal tape-cell encoding."""
import json
import random


def convert(word, mutant=None):
    raw=list(word)
    scratch=[]
    result=[]
    steps=0
    while raw:
        bit=raw.pop(0)
        scratch.insert(0,bit)
        steps+=1
    steps+=1
    while scratch:
        bit=scratch.pop(0)
        result=[True,bit]+result if mutant!='reversed_pair' else [bit,True]+result
        steps+=1
    steps+=1
    if mutant=='skip_head':return None,scratch,result,steps
    head=(result[1] if result[0] else None) if result else None
    result=result[2:]
    steps+=1
    return head,scratch,result,steps

cases=0
for seed in [7,19,41]:
    rng=random.Random(seed)
    for _ in range(1000):
        word=[bool(rng.randrange(2)) for _ in range(rng.randrange(65))]
        expected=(word[0] if word else None,[],[x for bit in word[1:] for x in [True,bit]],2*len(word)+3)
        assert convert(word)==expected
        cases+=1
fixture=[False,True,True]
assert convert(fixture,'reversed_pair')!=convert(fixture)
assert convert(fixture,'skip_head')!=convert(fixture)
assert convert([])==(None,[],[],3)
assert convert([False])==(False,[],[],5)
print(json.dumps(dict(cases=cases,seeds=[7,19,41],lengths=[0,64],failures=0,gaveUp=0,mutants=['reversed_pair','skip_head']),indent=2))
