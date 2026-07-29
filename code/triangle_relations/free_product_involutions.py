# Independent check of Theorem (Even strata)(iii): in W_m = D_m * C_2, exactly
# one of the k^2 words w_{a,b} squares to the identity, namely w_{0,k+1}.
# D_m elements as (j,e): g = s^j x_0^e, s = x_0x_1.  x_0=(0,1), x_1=(-1,1).
def mkD(m):
    def mul(g,h):
        j1,e1=g; j2,e2=h
        return ((j1 + (j2 if e1==0 else -j2)) % m, (e1+e2)%2)
    return mul
def word_syll(w, m):
    """free-product normal form: list of ('D',(j,e)) / ('C',) syllables."""
    mul=mkD(m); ID=(0,0)
    X={'0':(0,1),'1':((-1)%m,1)}
    out=[]
    def push(sy):
        if sy[0]=='D' and sy[1]==ID: return
        if out and out[-1][0]=='C' and sy[0]=='C': out.pop(); return
        if out and out[-1][0]=='D' and sy[0]=='D':
            g=mul(out.pop()[1], sy[1])
            if g!=ID: out.append(('D',g))
            return
        out.append(sy)
    for ch in w:
        push(('C',) if ch=='2' else ('D', X[ch]))
    return out
def sq_is_id(w, m):
    s=word_syll(w+w, m)
    return len(s)==0
def words(m):
    L,k=m+2,m//2
    res={}
    for a in range(k+1):
        for b in range(1,k+2):
            if b in (a,a+1): continue
            u=[('1' if i%2 else '0') for i in range(1,L+1)]
            u[2*a]='2'; u[2*b-1]='2'
            res[(a,b)]="".join(u)
    return res
for m in (4,6,8,10,12,14,16):
    k=m//2; W=words(m)
    inv=[ab for ab,w in W.items() if sq_is_id(w,m)]
    print(f"m={m:2d}: {len(W):3d} words (k^2={k*k:3d}); involutions in W_m: "
          f"{len(inv)} at {inv}  -> new relations {len(W)-len(inv):3d} "
          f"[(m/2)^2-1 = {k*k-1:3d}]  {'OK' if inv==[(0,k+1)] and len(W)-len(inv)==k*k-1 else 'MISMATCH'}")
