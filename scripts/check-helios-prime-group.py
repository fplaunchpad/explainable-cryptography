#!/usr/bin/env python3
"""Independent integer modular arithmetic for the proposed public group codec."""
import json

def encode(n):
    bits = [(n >> i) & 1 for i in range(n.bit_length())]
    return [1]*len(bits)+[0]+bits

def decode(p,q,word):
    try: k=word.index(0)
    except ValueError: return None
    bits=word[k+1:]
    if len(bits)!=k or (k and bits[-1]!=1): return None
    n=sum(b*2**i for i,b in enumerate(bits))
    if n>=p or pow(n,q,p)!=1: return None
    return n

# Independent expected subgroup for p=23, q=11; identity must be present.
expected={1,2,3,4,6,8,9,12,13,16,18}
assert {x for x in range(23) if pow(x,11,23)==1} == expected
assert decode(23,11,encode(1))==1
assert decode(23,11,encode(0)) is None
assert decode(23,11,encode(22)) is None
# Mutants: dropping subgroup membership, reducing aliases, excluding identity.
assert 22 < 23 and 22 not in expected
assert (24 % 23) in expected and decode(23,11,encode(24)) is None
assert 1 in expected

coordinates=operations=encryptions=malformed=0
for p,q,g in [(7,3,2),(11,5,3),(23,11,2),(47,23,2)]:
    subgroup={pow(g,r,p) for r in range(q)}
    assert len(subgroup)==q
    assert subgroup == {x for x in range(p) if pow(x,q,p)==1}
    for x in range(p+3):
        assert decode(p,q,encode(x))==(x if x in subgroup else None)
        coordinates+=1
        for bad in [encode(x)+[0], encode(x)+[1], encode(x)[:-1]]:
            assert decode(p,q,bad) is None
            malformed+=1
    for x in subgroup:
        assert pow(x,q,p)==1
        assert pow(x,p-2,p) in subgroup
        assert len(encode(x)) <= 2*(p-1).bit_length()+1
        for r in range(q):
            for s in range(q):
                assert pow(x,(r+s)%q,p)==pow(x,r,p)*pow(x,s,p)%p
                assert pow(pow(x,s,p),r,p)==pow(x,(r*s)%q,p)
                operations+=1
    for secret in range(1,q):
        key=pow(g,secret,p)
        for nonce in range(1,q):
            for vote in [0,1]:
                a=pow(g,nonce,p);b=pow(g,vote,p)*pow(key,nonce,p)%p
                assert (a in subgroup and b in subgroup)
                assert b*pow(pow(a,secret,p),p-2,p)%p==pow(g,vote,p)
                encryptions+=1
assert (pow(2,4,23),pow(2,1,23)*pow(8,4,23)%23)==(16,4)
print(json.dumps(dict(coordinates=coordinates,modular_action_checks=operations,
    encryptions=encryptions,malformed_records=malformed,
    detected_mutations=['missing_membership','modulo_alias','excluded_identity'],
    failures=0,gaveUp=0),indent=2))
