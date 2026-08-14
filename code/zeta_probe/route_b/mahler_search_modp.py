# Fast modular Mahler search on G0 (and reusable for V,U). Nullspace over GF(p).
import json
P=2147483647  # 2^31-1 prime
G0=[int(s)%P for s in json.load(open("/tmp/G0_long.json"))]
N=len(G0)-1

def series_pow(coeffs,d,i,M):
    e=d**i; out=[0]*(M+1)
    for n,c in enumerate(coeffs):
        if n*e<=M: out[n*e]=(out[n*e]+c)%P
        else: break
    return out

def rref_null(rows):
    M=[r[:] for r in rows]; nr=len(M); nc=len(M[0]) if M else 0
    pivcols=[]; r=0
    for c in range(nc):
        piv=None
        for rr in range(r,nr):
            if M[rr][c]: piv=rr;break
        if piv is None: continue
        M[r],M[piv]=M[piv],M[r]
        invv=pow(M[r][c],P-2,P)
        M[r]=[(x*invv)%P for x in M[r]]
        for rr in range(nr):
            if rr!=r and M[rr][c]:
                f=M[rr][c]; M[rr]=[(M[rr][k]-f*M[r][k])%P for k in range(nc)]
        pivcols.append(c); r+=1
        if r==nr: break
    free=[c for c in range(nc) if c not in pivcols]; basis=[]
    for fc in free:
        vec=[0]*nc; vec[fc]=1
        for ri,pc in enumerate(pivcols): vec[pc]=(-M[ri][fc])%P
        basis.append(vec)
    return basis

def test(data,d,m,D,fit_M,verify_to):
    nun=(m+1)*(D+1)
    fpow=[series_pow(data,d,i,fit_M) for i in range(m+1)]
    rows=[]
    for p in range(fit_M+1):
        row=[0]*nun
        for i in range(m+1):
            base=i*(D+1)
            fp=fpow[i]
            for j in range(D+1):
                if p-j>=0: row[base+j]=fp[p-j]
        rows.append(row)
    basis=rref_null(rows)
    if not basis: return None
    fpowN=[series_pow(data,d,i,verify_to) for i in range(m+1)]
    good=[]
    for vec in basis:
        ok=True
        for p in range(fit_M+1,verify_to+1):
            s=0
            for i in range(m+1):
                base=i*(D+1); fp=fpowN[i]
                for j in range(D+1):
                    if p-j>=0: s=(s+vec[base+j]*fp[p-j])%P
            if s: ok=False;break
        if ok: good.append(vec)
    return good

print("FAST modular (GF(2^31-1)) strict Mahler search on G0 (order q^%d)\n"%N)
found=False
import sys
for d in [2,3]:
    for m in range(1,8):
        if d**m > N//4: break
        for D in range(1,30):
            nun=(m+1)*(D+1)
            fit_M=nun+d**m+12
            verify_to=N
            if fit_M+25>verify_to: continue
            g=test(G0,d,m,D,fit_M,verify_to)
            if g:
                print(f"  d={d} m={m} D={D} nun={nun}: VERIFIED nullspace dim {len(g)} (fit q^{fit_M} verify q^{verify_to}) *** GENUINE ***")
                found=True;break
        if found: break
    if found: break
if not found:
    print("  NO genuine Mahler relation for G0 up to d=3, m=7, deg<=29, verified to q^%d."%N)
