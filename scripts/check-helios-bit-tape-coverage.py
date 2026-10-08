import json,random

def enc(c): return [c is not None,c is True]
def push(c,word): return enc(c)+word
def pop(word):
    if not word:return None,[]
    return (bool(word[1]) if word[0] else None),word[2:]
count=0
for seed in [7,19,41]:
    r=random.Random(seed)
    for _ in range(400):
        initial=[r.choice([None,False,True]) for _ in range(r.randrange(13))]
        tape=dict(enumerate(initial));pos=0
        head=tape.get(0);left=[];right=sum((enc(c) for c in initial[1:]),[])
        for _ in range(40):
            action=r.randrange(5)
            if action<3:
                head=[None,False,True][action];tape[pos]=head
            elif action==3:
                right=push(head,right);head,left=pop(left);pos-=1
            else:
                left=push(head,left);head,right=pop(right);pos+=1
            assert head is tape.get(pos)
            for offset in range(1,55):
                wl=left[2*(offset-1):2*offset];wr=right[2*(offset-1):2*offset]
                assert pop(wl)[0] is tape.get(pos-offset)
                assert pop(wr)[0] is tape.get(pos+offset)
            count+=1
assert pop([])[0] is None and pop(enc(False))[0] is False
def mutant_pop(word):
    return (False,[]) if not word else pop(word)
assert mutant_pop([]) != pop([])
def round_trip(drop_push=False):
    head=False
    left=[] if drop_push else push(head,[])
    head=None
    head,left=pop(left)
    return head
assert round_trip() is False
assert round_trip(drop_push=True) != round_trip()
print(json.dumps(dict(steps=count,paths=1200,seeds=[7,19,41],initial_lengths=[0,12],path_length=40,checked_offsets=54,failures=0,gaveUp=0,mutants=['missing_cell_false','dropped_push']),indent=2))
