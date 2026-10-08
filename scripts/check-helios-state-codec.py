#!/usr/bin/env python3
"""Independent ordered state and collision fixtures using integer coordinates."""
import contextlib,io,json,runpy
with contextlib.redirect_stdout(io.StringIO()):
    base=runpy.run_path('scripts/check-helios-cache-codec.py')
fields,number,cache,key=(base[x] for x in ['fields','number','cache','key'])
k=base['k'];other=tuple(reversed(k));stmt=k[:4];different=other[:4]

def statement(s):return fields([fields([number(s[0]),number(s[1])]),fields([number(s[2]),number(s[3])])])
def programmed(s):
    entries,bad,history=s
    return fields([cache(entries),fields([[int(bad)],fields([statement(x) for x in history])])])
def both(s,live):return fields([programmed(s),cache(live)])
def logged(entries,log):return fields([cache(entries),fields([key(x) for x in log])])
def program(s,st,commitment,answer):
    entries,bad,history=s;target=st+commitment
    if any(kk==target for kk,_ in entries):return entries,True,[st]+history
    return [(target,answer)]+entries,bad,[st]+history

def pair_bound(a,b):return 5+(2*a.bit_length()+1+a)+(2*b.bit_length()+1+b)
def list_bound(a,n):return 2*n.bit_length()+1+n*(2*a.bit_length()+1+a)
def cache_bound(n):return list_bound(base['E'],n)
SB=pair_bound(pair_bound(base['L'],base['L']),pair_bound(base['L'],base['L']))
def prog_bound(c,h):return pair_bound(cache_bound(c),pair_bound(1,list_bound(SB,h)))
checks=0
for flag in [False,True]:
    for answer in range(11):
        s=([(k,3)],flag,[different,stmt])
        # Every occupied key flags and retains the old answer, even on agreement.
        out=program(s,stmt,k[4:],answer)
        assert out==([(k,3)],True,[stmt,different,stmt])
        assert programmed(out)!=programmed((out[0],False,out[2]))
        assert programmed(out)!=programmed((out[0],True,[stmt,different]))
        fresh=program(s,different,other[4:],answer)
        assert fresh==([(other,answer),(k,3)],flag,[different,different,stmt])
        assert programmed(fresh)!=programmed((fresh[0],flag,list(reversed(fresh[2]))))
        assert both(out,[(other,answer)])!=both(out,[])
        for st in [s,out,fresh]:
            assert len(programmed(st))<=prog_bound(len(st[0]),len(st[2]))
            assert len(both(st,[(other,answer)]))<=pair_bound(prog_bound(len(st[0]),len(st[2])),cache_bound(1))
        checks+=1
assert logged([(k,3)],[k,other])!=logged([(k,3)],[other,k])
assert logged([(k,3)],[k,k])!=logged([(k,3)],[k])
assert len(logged([(k,3)],[k,other]))<=pair_bound(cache_bound(1),list_bound(base['K'],2))
print(json.dumps(dict(transitions=checks,detected_mutations=['clear_collision_flag',
    'deduplicate_history','reverse_history','erase_live_cache','reverse_miss_log'],failures=0,gaveUp=0),indent=2))
