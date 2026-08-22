"""Exact verification that the (1,2) right triangle first deviates from the
universal orbit-growth sequence A396406 at depth 33.

Side-reflection group of the right triangle with legs (1,2), breadth-first
search in exact arithmetic.  Group elements are stored as (a,b,c,d,x,y,k)
denoting the affine map with linear part [[a,b],[c,d]]/5^k and translation
(x,y)/5^k, reduced so that not all of a..y are divisible by 5.  All entries
lie in Z[1/5] because the three mirrors of this triangle have direction
vectors of squared length 1, 5 and 4.

    python3 deviation_1_2.py 33 out.json     (~40 s, ~3.2 GB peak)

Result: u_d agrees with A396406 for 0 <= d <= 32 and gives
u_33 = 3848354 against the universal 3848384, a deficit of 30.
Cited in Paper 1, section on effective universality.
"""
import sys, time, resource, hashlib, json

GENS = [(1,0,0,-1,0,0,0), (-3,-4,-4,3,8,4,1), (-1,0,0,1,0,0,0)]
I    = (1,0,0,1,0,0,0)

def comp(M, N):
    am,bm,cm,dm,xm,ym,km = M
    an,bn,cn,dn,xn,yn,kn = N
    p = 5**kn
    a = am*an+bm*cn; b = am*bn+bm*dn
    c = cm*an+dm*cn; d = cm*bn+dm*dn
    x = am*xn+bm*yn + p*xm
    y = cm*xn+dm*yn + p*ym
    k = km+kn
    while k > 0 and not (a%5 or b%5 or c%5 or d%5 or x%5 or y%5):
        a//=5; b//=5; c//=5; d//=5; x//=5; y//=5; k-=1
    return (a,b,c,d,x,y,k)

def key(M):
    return hashlib.blake2b(repr(M).encode(), digest_size=16).digest()

def run(dmax, outfile):
    seen = {key(I)}; front = [I]; seq = [1]; t0 = time.time()
    for d in range(1, dmax+1):
        new = []
        for M in front:
            for g in GENS:
                N = comp(g, M)
                kk = key(N)
                if kk not in seen:
                    seen.add(kk); new.append(N)
        seq.append(len(new)); front = new
        el = time.time()-t0
        rss = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss/(1024**3)
        eta = (el/ sum(seq)) * (sum(seq)*1.49**(dmax-d)) - el if d < dmax else 0
        print(f"  d={d:2d} u_d={len(new):9d} cum={len(seen):10d} {el:8.1f}s rss={rss:5.2f}GB eta~{eta/60:6.1f}min", flush=True)
        json.dump({"legs":[1,2],"depth_done":d,"u":seq}, open(outfile,"w"))
        if rss > 8.0:
            print("  ABORT: rss exceeded 8GB", flush=True); break
    return seq

if __name__ == "__main__":
    dmax = int(sys.argv[1]); out = sys.argv[2]
    s = run(dmax, out)
    print("seq:", s)
