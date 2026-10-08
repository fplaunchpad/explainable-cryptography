#!/usr/bin/env python3
"""Independent modular transcripts and full-context oracle request fixtures."""
import json
p,q,g,secret,nonce = 23,11,2,3,4
pk=pow(g,secret,p)
key=('key',g,pk,pow(g,nonce,p))
ct=(3,13)
share=pow(ct[0],secret,p)
commit=(pow(g,nonce,p),pow(ct[0],nonce,p))
partial=('decryption',g,pk,ct,share,commit)
assert key==('key',2,8,16)
assert partial==('decryption',2,8,(3,13),4,(16,12))
response=(nonce+5*secret)%q
assert response==8
assert pow(g,response,p)==commit[0]*pow(pk,5,p)%p
assert pow(ct[0],response,p)==commit[1]*pow(share,5,p)%p
assert pow(ct[0],response+1,p)!=commit[1]*pow(share,5,p)%p
# Every context component is observable to arbitrary fixed hash functions.
requests=[key,partial]
cases=0
for request in requests:
    for i in range(1,len(request)):
        other=list(request)
        old=other[i]
        other[i]=tuple(x+1 for x in old) if isinstance(old,tuple) else old+1
        other=tuple(other)
        table={request:5,other:7}
        assert table[request]!=table[other]
        # Dropping this coordinate is a mutant that cannot implement both hashes.
        bad1=request[:i]+request[i+1:]
        bad2=other[:i]+other[i+1:]
        assert bad1==bad2
        cases+=1
# A shared cache must keep hits but separate complete different requests.
cache={}
tape=iter([5,7])
answers=[]
for request in [key,partial,key,partial]:
    if request not in cache:cache[request]=next(tape)
    answers.append(cache[request])
assert answers==[5,7,5,7] and len(cache)==2
print(json.dumps(dict(modular_transcripts=2,context_mutations_detected=cases,
    mixed_requests=4,distinct_cache_entries=2,failures=0,gaveUp=0),indent=2))
