# k=0 sector block model; truncated integer power series in x, q=x^2
import sys
D=int(sys.argv[1]) if len(sys.argv)>1 else 26
def z(): return [0]*(D+1)
def mono(c,e):
    r=z()
    if 0<=e<=D: r[e]=c
    return r
def add(*a): return [sum(t) for t in zip(*a)]
def sc(c,a): return [c*u for u in a]
def mul(a,b):
    r=z()
    for i,u in enumerate(a):
        if u:
            for j in range(D+1-i): r[i+j]+=u*b[j]
    return r
NB=D//2+2
def model(ey):   # y = x^(2*ey)
    g=z(); Gr=z()
    for L in range(1,D+1):
        g=add(g,mono(1,2*L+2*ey*(L-1))); Gr=add(Gr,mono(1,2*L+2*ey*L))
    P=[z() for _ in range(NB+1)]
    for it in range(D+2):
        Pn=[z() for _ in range(NB+1)]
        for b in range(1,NB+1):
            acc=mono(1,2*b)
            for a in range(1,NB+1):
                acc=add(acc,mul(add(mono(1,2*max(a,b)),mul(mono(1,2*(a+b)),g)),P[a]))
            Pn[b]=mul(mono(2,2*b),acc)
        P=Pn
    S=z()
    for b in range(1,NB+1): S=add(S,mul(mono(1,2*b),P[b]))
    # states: (signed deposit at junction, weight series, kind)
    half=lambda s:[u//2 for u in s]
    Ls=[(0,mono(1,0),'E'),(0,mul(g,S),'Z')]+[(sg*2*a,half(P[a]),'N') for a in range(1,NB+1) for sg in (1,-1)]
    Rs=[(0,mono(1,0),'E'),(0,mul(Gr,S),'Z')]+[(sg*2*b,half(P[b]),'N') for b in range(1,NB+1) for sg in (1,-1)]
    gS=mul(g,S); GrqS=mul(mul(Gr,mono(1,2*ey)),S)  # y*Gr*S
    W=z()
    for e in (1,-1):
        for dl in (0,1):
            for (u,wl,kl) in Ls:
                for (v,wr,kr) in Rs:
                    j=max(abs(u-1+(e if dl==0 else 0)),abs(v-(e if dl==1 else 0)))
                    if j>D: continue
                    wr2=wr
                    if kr=='Z':
                        wr2=mul(Gr,S) if (e==1 and dl==0) else gS
                        if dl==0 and kl=='N':
                            if e==1: wr2=gS
                            elif u==2: wr2=mul(Gr,S)
                    W=add(W,mul(mono(1,j),mul(wl,wr2)))
    return W,P,S,g
V0=[1,2,1,0,1,4,6,4,7,18,27,26,34,68,111,128,165,276,446,574,765,1150,1789,2436,3342,4788,7211]
U0=[1,2,1,0,1,4,6,4,5,18,25,18,22,68,101,88,95,252,386,382,419,950,1431,1564,1762,3548,5257]
for ey,tr,nm in ((0,V0,'y=1'),(1,U0,'y=q')):
    W=model(ey)[0]; n=min(len(tr),D+1)
    print(nm,W[:n]); print(' truth',tr[:n],'MATCH' if W[:n]==tr[:n] else 'DIFF at '+str([i for i in range(n) if W[i]!=tr[i]][:5]))
