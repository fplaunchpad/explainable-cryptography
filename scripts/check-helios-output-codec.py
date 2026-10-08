#!/usr/bin/env python3
"""Independent integer/list fixtures for complete typed election observations."""
import contextlib,copy,io,json,runpy
with contextlib.redirect_stdout(io.StringIO()):base=runpy.run_path('scripts/check-helios-cache-codec.py')
number,fields=base['number'],base['fields']
def pair(a,b):return fields([a,b])
def two(c,x):return pair(c(x[0]),c(x[1]))
def ct(x):return two(number,x)
def branch(x):return pair(ct(x[:2]),two(number,x[2:]))
def proof(x):return two(branch,x)
def ballot(x):return pair(two(ct,x['ciphertexts']),pair(two(proof,x['proofs']),proof(x['overall'])))
def decision(d):return [[0,0],[0,1],[1,0]][d]
def entry(x):return pair(number(x[0]),ballot(x[1]))
def board(x):return fields([entry(e) for e in x])
def honest(x):return pair(two(decision,x[0]),board(x[1]))
def submission(x):return pair(honest(x['honest']),pair(ballot(x['ballot']),pair(decision(x['decision']),board(x['board']))))
def schnorr(c,x):return pair(c(x[0]),number(x[1]))
def params(x):return pair(ct((x['g'],x['pk'])),pair(schnorr(number,x['keyproof']),pair(fields([number(n) for n in x['candidates']]),fields([number(n) for n in x['voters']]))))
def prefix(x):return pair(params(x['parameters']),pair(number(x['fingerprint']),honest((x['decisions'],x['board']))))
def decoded(x):return [0] if x is None else [1]+number(x)
def result(x):return pair(prefix(x['prefix']),pair(ballot(x['ballot']),pair(decision(x['decision']),pair(board(x['board']),pair(two(ct,x['encrypted']),pair(two(number,x['shares']),pair(two(lambda z:schnorr(ct,z),x['decryption_proofs']),two(decoded,x['decoded']))))))))
pr=((1,2,3,4),(6,8,9,10))
b=dict(ciphertexts=((1,2),(3,4)),proofs=(pr,pr),overall=pr)
p=dict(parameters=dict(g=2,pk=8,keyproof=(16,3),candidates=[0,1],voters=[0,1,2]),fingerprint=21,decisions=(0,1),board=[(0,b)])
r=dict(prefix=p,ballot=b,decision=2,board=[(0,b)],encrypted=((1,2),(3,4)),shares=(6,8),decryption_proofs=(((9,12),3),((16,18),4)),decoded=(None,0))
assert decoded(None)==[0] and decoded(0)==[1,0] and decoded(None)!=decoded(0)
assert len(set(tuple(decision(i)) for i in range(3)))==3
mutations=[]
def changed(name,edit):
    x=copy.deepcopy(r);edit(x);assert result(x)!=result(r);mutations.append(name)
changed('aggregate_response',lambda x:x['ballot'].__setitem__('overall',(pr[0],(6,8,9,0))))
changed('voter_identifier',lambda x:x.__setitem__('board',[(1,b)]))
changed('rejection_decision',lambda x:x.__setitem__('decision',1))
changed('fingerprint',lambda x:x['prefix'].__setitem__('fingerprint',22))
changed('key_proof',lambda x:x['prefix']['parameters'].__setitem__('keyproof',(16,4)))
changed('share',lambda x:x.__setitem__('shares',(9,8)))
changed('decryption_proof',lambda x:x.__setitem__('decryption_proofs',(((9,12),4),((16,18),4))))
changed('decode_failure',lambda x:x.__setitem__('decoded',(0,0)))
changed('candidate_order',lambda x:x['prefix']['parameters'].__setitem__('candidates',[1,0]))
changed('voter_order',lambda x:x['prefix']['parameters'].__setitem__('voters',[1,0,2]))
changed('honest_decision',lambda x:x['prefix'].__setitem__('decisions',(1,1)))
changed('tally_ciphertext',lambda x:x.__setitem__('encrypted',((2,2),(3,4))))
assert board([(0,b),(1,b)])!=board([(1,b),(0,b)])
# No field-independent bound may erase the fingerprint's actual binary width.
assert len(prefix({**p,'fingerprint':2**128}))>len(prefix(p))
def P(a,b):return 5+(2*a.bit_length()+1+a)+(2*b.bit_length()+1+b)
def V(a,n):return 2*n.bit_length()+1+n*(2*a.bit_length()+1+a)
L=2*(23-1).bit_length()+1;M=2*(11-1).bit_length()+1
C=P(L,L);R=P(C,P(M,M));H=P(R,R);A=P(P(C,C),P(P(H,H),H));E=P(5,A)
def B(n):return V(E,n)
def S(n,k):return P(P(P(2,2),B(n)),P(A,P(2,B(k))))
assert len(proof(pr))<=H and len(ballot(b))<=A
size_cases=0
for n in range(3):
    for k in range(4):
        for d in range(3):
            out=dict(honest=((0,1),[(i%3,b) for i in range(n)]),ballot=b,
                decision=d,board=[(i%3,b) for i in range(k)])
            assert len(submission(out))<=S(n,k)
            size_cases+=1
print(json.dumps(dict(public_field_mutations=len(mutations),submission_size_cases=size_cases,detected_mutations=mutations,
    controls=['None_vs_zero','three_decisions','board_order','fingerprint_width'],failures=0,gaveUp=0),indent=2))
