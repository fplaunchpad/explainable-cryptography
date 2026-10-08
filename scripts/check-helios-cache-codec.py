#!/usr/bin/env python3
"""Independent canonical key/cache framing over integer public coordinates."""
import json

def number(n):
    bits=[(n>>i)&1 for i in range(n.bit_length())]
    return [1]*len(bits)+[0]+bits

def read(word):
    if 0 not in word: return None
    width=word.index(0); payload=word[width+1:]
    if len(payload)<width: return None
    bits=payload[:width]
    if width and not bits[-1]: return None
    return sum(b<<i for i,b in enumerate(bits)),payload[width:]

def fields(xs):
    return number(len(xs))+sum((number(len(x))+x for x in xs),[])

def parse(word):
    nrest=read(word)
    if nrest is None: return None
    n,rest=nrest; out=[]
    for _ in range(n):
        result=read(rest)
        if result is None:return None
        k,rest=result
        if len(rest)<k:return None
        out.append(rest[:k]);rest=rest[k:]
    return out if not rest else None

def scalar(word,q):
    result=read(word)
    if result is None:return None
    n,rest=result
    return n if not rest and n<q else None

def key(k):return fields([number(x) for x in k])
def decode_key(word):
    xs=parse(word)
    if xs is None or len(xs)!=8:return None
    k=[scalar(x,23) for x in xs]
    if any(x is None or pow(x,11,23)!=1 for x in k):return None
    return tuple(k)

def entry(k,a):return fields([key(k),number(a)])
def cache(entries):return fields([entry(k,a) for k,a in entries])
def decode_cache(word,duplicates=False):
    xs=parse(word)
    if xs is None:return None
    entries=[]; seen=set()
    for x in xs:
        pair=parse(x)
        if pair is None or len(pair)!=2:return None
        k=decode_key(pair[0]);a=scalar(pair[1],11)
        if k is None or a is None or (not duplicates and k in seen):return None
        seen.add(k);entries.append((k,a))
    return entries

k=(1,2,3,4,6,8,9,12)
assert parse([0])==[]
assert fields([[1],[0]])==[1,1,0,0,1,1,0,1,1,1,0,1,0]
assert decode_key(key(k))==k
# Each of the eight fields is load-bearing, including generator and public key.
changed=[]
for i in range(8):
    m=list(k);m[i]=18 if m[i]!=18 else 16;m=tuple(m)
    assert decode_key(key(m))==m and key(m)!=key(k)
    changed.append(m)
assert decode_key(fields([number(x) for x in k[1:]])) is None
assert decode_key(fields([number(x) for x in k+(16,)])) is None
L=2*(23-1).bit_length()+1
S=2*(11-1).bit_length()+1
K=9+8*(2*L.bit_length()+1+L)
E=5+(2*K.bit_length()+1+K)+(2*S.bit_length()+1+S)
assert all(len(key(x))<=K for x in [k]+changed)
cases=bad=0
for n in range(10):
    ks=[k]+changed
    es=[(ks[i],i%11) for i in range(n)]
    word=cache(es)
    assert decode_cache(word)==es
    assert len(word)==2*n.bit_length()+1+sum(2*len(entry(x,a)).bit_length()+1+len(entry(x,a)) for x,a in es)
    assert all(len(entry(x,a))<=E for x,a in es)
    assert len(word)<=2*n.bit_length()+1+n*(2*E.bit_length()+1+E)
    cases+=1
    for malformed in [word+[0],word+[1],word[:-1]]:
        assert decode_cache(malformed) is None
        bad+=1
for a in range(11):
    word=cache([(k,a),(k,(a+1)%11)])
    assert decode_cache(word) is None
    assert decode_cache(word,duplicates=True) is not None
    bad+=1
assert decode_cache(cache([(k,11)])) is None
assert decode_cache(cache([(k,10)]))==[(k,10)]
print(json.dumps(dict(caches=cases,key_field_mutations=8,malformed_records=bad,
    detected_mutations=['omit_key_field','duplicate_keys','ignore_trailing'],failures=0,gaveUp=0),indent=2))
