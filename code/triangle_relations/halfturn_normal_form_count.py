# Verify: #{reduced words of length m+2 with c_1 = +m/2 and c_2 = 0} = (m/2)^2,
# and that the normal form is "odds are 1 except one '2' at 2a+1; evens are 0
# except one '2' at 2b; b not in {a, a+1}".
from itertools import product
def brute(m):
    L, k = m+2, m//2
    out=[]
    def rec(w):
        if len(w)==L:
            c1=sum((1 if i%2==0 else -1) for i,ch in enumerate(w) if ch=='1')
            c2=sum((1 if i%2==0 else -1) for i,ch in enumerate(w) if ch=='2')
            if c2==0 and c1==k: out.append("".join(w))
            return
        for ch in "012":
            if not w or w[-1]!=ch: rec(w+[ch])
    rec([])
    return sorted(out)
def formula(m):
    L, k = m+2, m//2
    out=[]
    for a in range(k+1):
        for b in range(1, k+2):
            if b in (a, a+1): continue
            w=[None]*L
            for i in range(1, L+1):
                w[i-1] = ('1' if i%2 else '0')
            w[2*a] = '2'      # position 2a+1 (1-indexed)
            w[2*b-1] = '2'    # position 2b
            out.append("".join(w))
    return sorted(out)
for m in (4,6,8,10,12,14):
    k=m//2
    b = brute(m) if m<=12 else None
    f = formula(m)
    ok = (b==f) if b is not None else "skipped"
    print(f"m={m:2d}: k^2={k*k:3d}  formula gives {len(f):3d}  brute {len(b) if b else '-':>4}  match={ok}")
print("\nm=4 words:", formula(4))
print("Coxeter one r_2 s^k r_2 for m=4:", "2"+"01"*2+"2")
