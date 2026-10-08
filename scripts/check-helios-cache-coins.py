#!/usr/bin/env python3
"""Actual scalar-prefix output is passed into independently interpreted cache operations."""
import contextlib
import io
import itertools
import json
import runpy
with contextlib.redirect_stdout(io.StringIO()):
    old=runpy.run_path('scripts/check-helios-cache-hash.py')
    scalar=runpy.run_path('scripts/check-helios-coin-scalar.py')


def driver(key, word, log, tape, width=4, mutant=None):
    found,_,_=old['cache_read']['machine'](key,word)
    if found[0]:
        value,_=old['log_append']['prefix'](found[1],[])
        return value,word,log,(1 if mutant=='hit_coin' else 0)
    coins=tape[:width]
    state,used,_,_=scalar['execute'](coins,11)
    value=state[5]
    if mutant=='wrong_word':value=[False]
    ok,inserted,_=old['insertion']['machine'](key,value,word)
    assert ok
    updated=old['log_append']['machine'](key,log,'prepend' if mutant=='prepend' else None)[0]
    return value,inserted[7],updated,used


def check(key, entries, log, tape, mutant=None):
    found=next((a for k,a in entries if k==key),None)
    if found is None:
        value=sum(int(b)<<i for i,b in enumerate(tape[:4]))%11
        entries=[(key,value)]+entries
        log=log+[key]
        used=4
    else:
        value=found
        used=0
    expected=(old['log_append']['nat'](value),old['encode_cache'](entries),old['log_append']['encode'](log),used)
    return expected


keys=[[],[False],[True]]
for mutant in ['hit_coin','wrong_word','prepend']:
    entries=[([False],6)] if mutant=='hit_coin' else []
    args=([False],entries,[[True]],[False,True,True,False,True])
    actual=driver(args[0],old['encode_cache'](args[1]),old['log_append']['encode'](args[2]),args[3],mutant=mutant)
    assert actual!=check(*args), 'undetected '+mutant
count=0
for entries in [[],[([],1)],[([False],6)],[([True],0),([],6)]]:
    for key,log,tape in itertools.product(keys,[[],[[True]],[[False],[True]]],itertools.product([False,True],repeat=4)):
        tape=list(tape)+[True,False]
        actual=driver(key,old['encode_cache'](entries),old['log_append']['encode'](log),tape)
        assert actual==check(key,entries,log,tape)
        count+=1
print(json.dumps(dict(exhaustive=count,modulus=11,coin_width=4,max_initial_entries=2,
    detected_mutants=['hit_coin','wrong_word','prepend'],failures=0,gaveUp=0),indent=2))
