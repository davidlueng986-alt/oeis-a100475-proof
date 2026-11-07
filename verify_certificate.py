"""Independent exact check of the COMPLETE finite reduction in PROOF.md.

Prime enumeration uses Eratosthenes, independent of generator trial division.
Digit reversal uses strings, independent of arithmetic digit extraction.
Ranks are checked locally, and a second Kahn graph elimination checks no
directed cycle remains. This file imports no generator or search library.
"""
import argparse,collections,csv,hashlib,json,math,pathlib
p=argparse.ArgumentParser();p.add_argument('--certificate',type=pathlib.Path,default=pathlib.Path('certificate.tsv'));p.add_argument('--output',type=pathlib.Path,default=pathlib.Path('verification.json'));args=p.parse_args()
raw=args.certificate.read_bytes();rows=list(csv.DictReader(raw.decode().splitlines(),delimiter='\t'))
B=60000;assert len(rows)==B
rows=[{k:int(v) for k,v in row.items()} for row in rows]
assert [r['n'] for r in rows]==list(range(1,B+1))
last=rows[-1]['p_n'];assert 2<=last<1000000
sieve=bytearray(b'\1')*(last+1);sieve[:2]=b'\0\0'
for d in range(2,math.isqrt(last)+1):
    if sieve[d]:sieve[d*d:last+1:d]=b'\0'*((last-d*d)//d+1)
primes=[d for d in range(2,last+1) if sieve[d]]
assert len(primes)==B
f=[0]+[int(str(q)[::-1]) for q in primes]
rank=[0]+[r['exit_steps'] for r in rows]
for n,row in enumerate(rows,1):
    assert row['p_n']==primes[n-1] and row['F_n']==f[n]
    assert 1<=rank[n]<=B and f[n]>0
    if f[n]<=B:assert rank[n]==1+rank[f[n]]
    else:assert rank[n]==1
# Independent cycle elimination on the finite directed graph, without ranks.
indeg=[0]*(B+1)
for n in range(1,B+1):
    if f[n]<=B:indeg[f[n]]+=1
queue=collections.deque(n for n in range(1,B+1) if indeg[n]==0);removed=0
while queue:
    n=queue.popleft();removed+=1
    if f[n]<=B:
        indeg[f[n]]-=1
        if indeg[f[n]]==0:queue.append(f[n])
assert removed==B
# Exact auxiliary integer inequality used with the standard theorem e<3.
assert 3**10<B
for q in primes:assert q%10!=0
out={'passed':True,'bound':B,'certificate_rows':len(rows),'prime_count':len(primes),'last_prime':last,
     'max_exit_steps':max(rank),'vertices_removed_by_independent_kahn_check':removed,
     'certificate_sha256':hashlib.sha256(raw).hexdigest(),
     'scope':'complete finite obligation for universal proof in PROOF.md, not a stand-alone infinite theorem',
     'external_mathematical_input':'Rosser theorem p_n>n log(n), and elementary e<3; bridges proved in PROOF.md'}
args.output.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
