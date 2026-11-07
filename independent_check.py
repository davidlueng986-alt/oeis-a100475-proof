"""Independently written A100475 verifier (no input from original certificate)."""
from collections import deque
from hashlib import sha256
import json
B = 60000
LIM = 1000000
sieve = bytearray([1]) * (LIM + 1)
sieve[0] = sieve[1] = 0
for p in range(2, int(LIM**0.5)+1):
    if sieve[p]:
        # unoptimized but independent indexing from supplied check
        m = p * p
        while m <= LIM:
            sieve[m] = 0
            m += p
primes = [i for i in range(LIM + 1) if sieve[i]][:B]
assert len(primes)==B
assert primes[-1] == 746773

def reverse_integer_decimal(v):
    digits=[]
    while v>0:
        digits.append(v%10)
        v//=10
    out=0
    for d in digits:
        out=out*10+d
    return out
F = [0]+[reverse_integer_decimal(q) for q in primes]
assert min(F[1:])>=1
assert len(F)==B+1
# Topological trim in functional graph, built independently from scratch
indeg=[0]*(B+1)
for i in range(1,B+1):
    j=F[i]
    if j<=B:
        indeg[j]+=1
queue=deque(i for i in range(1,B+1) if indeg[i]==0)
order=[]
while queue:
    i=queue.popleft()
    order.append(i)
    j=F[i]
    if j<=B:
        indeg[j]-=1
        if indeg[j]==0:
            queue.append(j)
assert len(order)==B
# Compute maximum steps to escape using reverse topo order
steps=[0]*(B+1)
for i in order[::-1]:
    nxt=F[i]
    steps[i]=1 if nxt>B else steps[nxt]+1
assert min(steps[1:])>=1
assert max(steps[1:])==10
# Explicit checking of all 60k starts, independent of original rank data
for i in range(1,B+1):
    x=i
    for t in range(steps[i]):
        x=F[x]
        if x>B:
            break
    assert x>B
assert all(q%10!=0 for q in primes)
result={
    'passed':True, 'B':B,'prime_last':primes[-1], 'vertices_topologically_eliminated':len(order),
    'max_steps_to_escape':max(steps[1:]),'num_1_step':steps[1:].count(1),'num_10_step':steps[1:].count(10),
    'certificate_independent':True,'same_certificate_read':False,'scope':'Independent finite component only; infinite proof requires Rosser bound and digit-length argument'
}
print(json.dumps(result,indent=2))
open('independent_second_audit.json','w').write(json.dumps(result,indent=2)+'\n')
