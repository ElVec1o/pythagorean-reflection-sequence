"""Full 3-stage crossing engine in high-precision FLOAT (mpmath). Returns A_1..A_MW."""
import os,sys
from mpmath import mp, mpf

def run(dps, NEPS, WNUM, MW):
    mp.dps=dps
    p=None
    inv=lambda a: mpf(1)/a
    def padd(a,b):
        n=max(len(a),len(b)); r=[mpf(0)]*n
        for i,x in enumerate(a): r[i]=(r[i]+x)
        for i,x in enumerate(b): r[i]=(r[i]+x)
        return r
    def pmul(a,b):
        if not a or not b: return [mpf(0)]
        r=[mpf(0)]*(len(a)+len(b)-1)
        for i,x in enumerate(a):
            if x:
                for j,y in enumerate(b): r[i+j]=(r[i+j]+x*y)
        return r
    def ps(a,c): return [(x*c) for x in a]
    # ---- stage 1: ell_n(i), Faulhaber, c_n(k) ----
    pm=[[mpf(1)]]
    for m in range(1,NEPS+1):
        q=[mpf(1)]
        for r in range(1,m+1): q=pmul(q,[(-r),1])
        f=mpf(1)
        for t in range(2,m+2): f=f*t
        pm.append(ps(q,inv(f)))
    X=[None]+[ps(pm[m],mpf((-1)**m)) for m in range(1,NEPS+1)]
    ell=[None]+[[mpf(0)] for _ in range(NEPS)]
    cur={m:X[m] for m in range(1,NEPS+1)}
    for r in range(1,NEPS+1):
        if r>1:
            new={}
            for m1,c1 in cur.items():
                for m2 in range(1,NEPS+1-m1):
                    k=m1+m2
                    new[k]=padd(new.get(k,[mpf(0)]),pmul(c1,X[m2]))
            cur=new
        s=mpf((-1)**(r+1))*inv(r)
        for m,cc in cur.items():
            if m<=NEPS: ell[m]=padd(ell[m],ps(cc,s))
    def faulhaber(d):
        pts=[(M,sum(mpf(i)**d for i in range(1,M+1))) for M in range(0,d+3)]
        n=d+2
        A=[[mpf(pt[0])**j for j in range(n)] for pt in pts[:n]]; y=[pt[1] for pt in pts[:n]]
        for c_ in range(n):
            pv=next(rr for rr in range(c_,n) if A[rr][c_]!=0)
            A[c_],A[pv]=A[pv],A[c_]; y[c_],y[pv]=y[pv],y[c_]
            iv=inv(A[c_][c_]); A[c_]=[v*iv for v in A[c_]]; y[c_]=y[c_]*iv
            for rr in range(n):
                if rr!=c_ and A[rr][c_]!=0:
                    f=A[rr][c_]; A[rr]=[(v-f*w) for v,w in zip(A[rr],A[c_])]; y[rr]=(y[rr]-f*y[c_])
        return y
    FH=[faulhaber(d) for d in range(NEPS+2)]
    def sm(poly):
        out=[mpf(0)]
        for d,cc in enumerate(poly):
            if cc: out=padd(out,ps(FH[d],cc))
        return out
    def s2k(pM): return [(cc*mpf(2)**d) for d,cc in enumerate(pM)]
    c=[None]
    for n in range(1,NEPS+1):
        Ln=s2k(sm(ell[n]))
        cn=padd(ps([mpf(0),mpf(-1),mpf(1)],-inv(n)),ps(Ln,mpf(-1)))
        c.append(cn)
    # ---- stage 2: E_j, D-actions ----
    res={0:[mpf(1)]}; pcur={0:[mpf(1)]}
    S={n:c[n] for n in range(2,NEPS+1)}
    for r in range(1,NEPS//2+1):
        new={}
        for e1,c1 in pcur.items():
            for n,cn in S.items():
                e=e1+n
                if e<=NEPS: new[e]=padd(new.get(e,[mpf(0)]),pmul(c1,cn))
        pcur=new
        if not pcur: break
        invf=mpf(1)
        for t in range(1,r+1): invf=invf*inv(t)
        for e,cc in pcur.items(): res[e]=padd(res.get(e,[mpf(0)]),ps(cc,invf))
    E=res
    maxdeg=max(len(E[j])-1 for j in E)
    Ap=[[mpf(0)]]; Bp=[[mpf(1)]]
    h=inv(2)
    for _ in range(maxdeg+1):
        A0,B0=Ap[-1],Bp[-1]
        dA=[(A0[i+1]*(i+1)) for i in range(len(A0)-1)] or [mpf(0)]
        dB=[(B0[i+1]*(i+1)) for i in range(len(B0)-1)] or [mpf(0)]
        nA=ps(pmul([0,1],padd(dA,ps(B0,mpf(-1)))),h)
        nB=ps(pmul([0,1],padd(dB,A0)),h)
        Ap.append(nA); Bp.append(nB)
    At={};Bt={}
    for j,Ej in E.items():
        a=[mpf(0)];b=[mpf(0)]
        for d,cf in enumerate(Ej):
            if cf: a=padd(a,ps(Ap[d],cf)); b=padd(b,ps(Bp[d],cf))
        At[j]=a; Bt[j]=b
    # ---- stage 3: graded delta solve, m-eq, reversion ----
    keep=lambda a,b: 2*a-b<=WNUM and a<=NEPS
    def sadd(s1,s2):
        r=dict(s1)
        for k,v in s2.items():
            r[k]=(r.get(k,0)+v)
            if r[k]==0: del r[k]
        return r
    def smul(s1,s2):
        r={}
        for (a1,b1),v1 in s1.items():
            for (a2,b2),v2 in s2.items():
                a,b=a1+a2,b1+b2
                if keep(a,b):
                    k=(a,b); r[k]=(r.get(k,0)+v1*v2)
                    if r[k]==0: del r[k]
        return r
    def sscale(s,cst): return {k:(v*cst) for k,v in s.items()} if cst else {}
    def derivs(poly,rmax):
        out=[poly[:]]; cur2=poly[:]
        for _ in range(rmax):
            cur2=[(cur2[i+1]*(i+1)) for i in range(len(cur2)-1)] or [mpf(0)]
            out.append(cur2[:])
        return out
    def p2s(poly,ep):
        s={}
        for b,cv in enumerate(poly):
            if cv and keep(ep,b): s[(ep,b)]=cv
        return s
    DMAX=WNUM
    Phi=[{} for _ in range(DMAX+1)]
    fact=[mpf(1)]
    for i in range(1,DMAX+2): fact.append(fact[-1]*i)
    for j in sorted(At):
        if j>NEPS: continue
        Ad=derivs(At[j],DMAX); Bd=derivs(Bt[j],DMAX)
        for d in range(DMAX+1):
            acc={}
            for r in range(d+1):
                t=d-r
                if t%2==0:
                    cv=((-1)**(t//2))*inv(fact[t])*inv(fact[r])
                    acc=sadd(acc,sscale(p2s(Ad[r],j),cv))
                else:
                    cv=(-((-1)**((t-1)//2)))*inv(fact[t])*inv(fact[r])
                    acc=sadd(acc,sscale(p2s(Bd[r],j),cv))
            Phi[d]=sadd(Phi[d],acc)
    def phi_eval(delta):
        r=dict(Phi[0]); cur2={(0,0):mpf(1)}
        for d in range(1,DMAX+1):
            cur2=smul(cur2,delta)
            if not cur2: break
            for k,v in smul(Phi[d],cur2).items():
                r[k]=(r.get(k,0)+v)
                if r[k]==0: del r[k]
        return r
    def phi_prime(delta):
        r=dict(Phi[1]); cur2={(0,0):mpf(1)}
        for d in range(2,DMAX+1):
            cur2=smul(cur2,delta)
            if not cur2: break
            for k,v in smul(sscale(Phi[d],d),cur2).items():
                r[k]=(r.get(k,0)+v)
                if r[k]==0: del r[k]
        return r
    def sinv(s):
        c0=s.get((0,0))
        rest=sscale({k:v for k,v in s.items() if k!=(0,0)},inv(c0))
        out={(0,0):inv(c0)}; powr={(0,0):mpf(1)}
        for r in range(1,2*WNUM+2):
            powr=smul(powr,rest)
            if not powr: break
            out=sadd(out,sscale(powr,mpf((-1)**r)*inv(c0)))
        return out
    delta={}
    for _ in range(WNUM+3):
        F=phi_eval(delta)
        if not F: break
        delta=sadd(delta,sscale(smul(F,sinv(phi_prime(delta))),mpf(-1)))
    T={(1,2):mpf(1)}
    T=sadd(T,sscale(smul({(1,1):mpf(1)},delta),2))
    T=sadd(T,smul({(1,0):mpf(1)},smul(delta,delta)))
    es=[mpf(1)]
    for n in range(1,NEPS+1): es.append(es[-1]*inv(2)*inv(n))
    ex={}
    for a in range(NEPS+1):
        v=2*(es[a]-(es[a-1] if a>=1 else mpf(0)))
        if v: ex[(a,0)]=v
    T=sadd(T,sscale(ex,mpf(-1)))
    P={}
    for (a,b),v in T.items():
        if b%2: continue
        cc=b//2; ae=a-cc
        if 0<=ae<=MW: P[(ae,cc)]=(P.get((ae,cc),0)+v)
    mser=[mpf(2)]+[mpf(0)]*MW
    for order in range(1,MW+1):
        def mpow(cn,n):
            dp=[mpf(0)]*(n+1); dp[0]=mpf(1)
            for _ in range(cn):
                nd=[mpf(0)]*(n+1)
                for i in range(n+1):
                    if dp[i]:
                        for jj in range(n+1-i): nd[i+jj]=(nd[i+jj]+dp[i]*mser[jj])
                dp=nd
            return dp[n]
        F0=mpf(0)
        for (ae,cc),v in P.items():
            if ae<=order: F0=(F0+v*mpow(cc,order-ae))
        dF=mpf(0)
        for (ae,cc),v in P.items():
            if ae==0 and cc>=1: dF=(dF+v*cc*mpf(2)**(cc-1))
        mser[order]=-F0*inv(dF)
    ex_=[mpf(0),mpf(2)]+[mpf(0)]*(MW+1)
    for order in range(2,MW+2):
        def epow(pw,n):
            dp=[mpf(0)]*(n+1); dp[0]=mpf(1)
            for _ in range(pw):
                nd=[mpf(0)]*(n+1)
                for i in range(n+1):
                    if dp[i]:
                        for jj in range(1,n+1-i): nd[i+jj]=(nd[i+jj]+dp[i]*(ex_[jj] if jj<len(ex_) else 0))
                dp=nd
            return dp[n]
        tot=mpf(0)
        for pw in range(0,MW+1):
            if pw<len(mser) and mser[pw]: tot=(tot+mser[pw]*epow(pw,order-1))
        while len(ex_)<=order: ex_.append(0)
        ex_[order]=tot
    return [ex_[n+1]*inv(2) for n in range(1,MW+1)]
if __name__=="__main__":
    order=int(sys.argv[2]); A=run(int(sys.argv[1]),4*order,2*order+1,order)
    print(" ".join(mp.nstr(x,25) for x in A))
