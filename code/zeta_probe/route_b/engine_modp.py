"""Full 3-stage crossing engine mod p. Returns A_1..A_MW mod p."""
import os,sys
def run(p, NEPS, WNUM, MW):
    inv=lambda a: pow(a%p,p-2,p)
    def padd(a,b):
        n=max(len(a),len(b)); r=[0]*n
        for i,x in enumerate(a): r[i]=(r[i]+x)%p
        for i,x in enumerate(b): r[i]=(r[i]+x)%p
        return r
    def pmul(a,b):
        if not a or not b: return [0]
        r=[0]*(len(a)+len(b)-1)
        for i,x in enumerate(a):
            if x:
                for j,y in enumerate(b): r[i+j]=(r[i+j]+x*y)%p
        return r
    def ps(a,c): return [(x*c)%p for x in a]
    # ---- stage 1: ell_n(i), Faulhaber, c_n(k) ----
    pm=[[1]]
    for m in range(1,NEPS+1):
        q=[1]
        for r in range(1,m+1): q=pmul(q,[(-r)%p,1])
        f=1
        for t in range(2,m+2): f=f*t%p
        pm.append(ps(q,inv(f)))
    X=[None]+[ps(pm[m],(-1)**m%p) for m in range(1,NEPS+1)]
    ell=[None]+[[0] for _ in range(NEPS)]
    cur={m:X[m] for m in range(1,NEPS+1)}
    for r in range(1,NEPS+1):
        if r>1:
            new={}
            for m1,c1 in cur.items():
                for m2 in range(1,NEPS+1-m1):
                    k=m1+m2
                    new[k]=padd(new.get(k,[0]),pmul(c1,X[m2]))
            cur=new
        s=((-1)**(r+1))*inv(r)%p
        for m,cc in cur.items():
            if m<=NEPS: ell[m]=padd(ell[m],ps(cc,s))
    def faulhaber(d):
        pts=[(M,sum(pow(i,d,p) for i in range(1,M+1))%p) for M in range(0,d+3)]
        n=d+2
        A=[[pow(pt[0],j,p) for j in range(n)] for pt in pts[:n]]; y=[pt[1] for pt in pts[:n]]
        for c_ in range(n):
            pv=next(rr for rr in range(c_,n) if A[rr][c_]%p)
            A[c_],A[pv]=A[pv],A[c_]; y[c_],y[pv]=y[pv],y[c_]
            iv=inv(A[c_][c_]); A[c_]=[v*iv%p for v in A[c_]]; y[c_]=y[c_]*iv%p
            for rr in range(n):
                if rr!=c_ and A[rr][c_]%p:
                    f=A[rr][c_]; A[rr]=[(v-f*w)%p for v,w in zip(A[rr],A[c_])]; y[rr]=(y[rr]-f*y[c_])%p
        return y
    FH=[faulhaber(d) for d in range(NEPS+2)]
    def sm(poly):
        out=[0]
        for d,cc in enumerate(poly):
            if cc: out=padd(out,ps(FH[d],cc))
        return out
    def s2k(pM): return [(cc*pow(2,d,p))%p for d,cc in enumerate(pM)]
    c=[None]
    for n in range(1,NEPS+1):
        Ln=s2k(sm(ell[n]))
        cn=padd(ps([0,(-1)%p,1],(-inv(n))%p),ps(Ln,(-1)%p))
        c.append(cn)
    # ---- stage 2: E_j, D-actions ----
    res={0:[1]}; pcur={0:[1]}
    S={n:c[n] for n in range(2,NEPS+1)}
    for r in range(1,NEPS//2+1):
        new={}
        for e1,c1 in pcur.items():
            for n,cn in S.items():
                e=e1+n
                if e<=NEPS: new[e]=padd(new.get(e,[0]),pmul(c1,cn))
        pcur=new
        if not pcur: break
        invf=1
        for t in range(1,r+1): invf=invf*inv(t)%p
        for e,cc in pcur.items(): res[e]=padd(res.get(e,[0]),ps(cc,invf))
    E=res
    maxdeg=max(len(E[j])-1 for j in E)
    Ap=[[0]]; Bp=[[1]]
    h=inv(2)
    for _ in range(maxdeg+1):
        A0,B0=Ap[-1],Bp[-1]
        dA=[(A0[i+1]*(i+1))%p for i in range(len(A0)-1)] or [0]
        dB=[(B0[i+1]*(i+1))%p for i in range(len(B0)-1)] or [0]
        nA=ps(pmul([0,1],padd(dA,ps(B0,(-1)%p))),h)
        nB=ps(pmul([0,1],padd(dB,A0)),h)
        Ap.append(nA); Bp.append(nB)
    At={};Bt={}
    for j,Ej in E.items():
        a=[0];b=[0]
        for d,cf in enumerate(Ej):
            if cf: a=padd(a,ps(Ap[d],cf)); b=padd(b,ps(Bp[d],cf))
        At[j]=a; Bt[j]=b
    # ---- stage 3: graded delta solve, m-eq, reversion ----
    keep=lambda a,b: 2*a-b<=WNUM and a<=NEPS
    def sadd(s1,s2):
        r=dict(s1)
        for k,v in s2.items():
            r[k]=(r.get(k,0)+v)%p
            if r[k]==0: del r[k]
        return r
    def smul(s1,s2):
        r={}
        for (a1,b1),v1 in s1.items():
            for (a2,b2),v2 in s2.items():
                a,b=a1+a2,b1+b2
                if keep(a,b):
                    k=(a,b); r[k]=(r.get(k,0)+v1*v2)%p
                    if r[k]==0: del r[k]
        return r
    def sscale(s,cst): return {k:(v*cst)%p for k,v in s.items()} if cst%p else {}
    def derivs(poly,rmax):
        out=[poly[:]]; cur2=poly[:]
        for _ in range(rmax):
            cur2=[(cur2[i+1]*(i+1))%p for i in range(len(cur2)-1)] or [0]
            out.append(cur2[:])
        return out
    def p2s(poly,ep):
        s={}
        for b,cv in enumerate(poly):
            if cv and keep(ep,b): s[(ep,b)]=cv
        return s
    DMAX=WNUM
    Phi=[{} for _ in range(DMAX+1)]
    fact=[1]
    for i in range(1,DMAX+2): fact.append(fact[-1]*i%p)
    for j in sorted(At):
        if j>NEPS: continue
        Ad=derivs(At[j],DMAX); Bd=derivs(Bt[j],DMAX)
        for d in range(DMAX+1):
            acc={}
            for r in range(d+1):
                t=d-r
                if t%2==0:
                    cv=((-1)**(t//2))*inv(fact[t])%p*inv(fact[r])%p
                    acc=sadd(acc,sscale(p2s(Ad[r],j),cv))
                else:
                    cv=(-((-1)**((t-1)//2)))*inv(fact[t])%p*inv(fact[r])%p
                    acc=sadd(acc,sscale(p2s(Bd[r],j),cv))
            Phi[d]=sadd(Phi[d],acc)
    def phi_eval(delta):
        r=dict(Phi[0]); cur2={(0,0):1}
        for d in range(1,DMAX+1):
            cur2=smul(cur2,delta)
            if not cur2: break
            for k,v in smul(Phi[d],cur2).items():
                r[k]=(r.get(k,0)+v)%p
                if r[k]==0: del r[k]
        return r
    def phi_prime(delta):
        r=dict(Phi[1]); cur2={(0,0):1}
        for d in range(2,DMAX+1):
            cur2=smul(cur2,delta)
            if not cur2: break
            for k,v in smul(sscale(Phi[d],d),cur2).items():
                r[k]=(r.get(k,0)+v)%p
                if r[k]==0: del r[k]
        return r
    def sinv(s):
        c0=s.get((0,0))
        rest=sscale({k:v for k,v in s.items() if k!=(0,0)},inv(c0))
        out={(0,0):inv(c0)}; powr={(0,0):1}
        for r in range(1,2*WNUM+2):
            powr=smul(powr,rest)
            if not powr: break
            out=sadd(out,sscale(powr,((-1)**r)*inv(c0)%p))
        return out
    delta={}
    for _ in range(WNUM+3):
        F=phi_eval(delta)
        if not F: break
        delta=sadd(delta,sscale(smul(F,sinv(phi_prime(delta))),(-1)%p))
    T={(1,2):1}
    T=sadd(T,sscale(smul({(1,1):1},delta),2))
    T=sadd(T,smul({(1,0):1},smul(delta,delta)))
    es=[1]
    for n in range(1,NEPS+1): es.append(es[-1]*inv(2)%p*inv(n)%p)
    ex={}
    for a in range(NEPS+1):
        v=(2*(es[a]-(es[a-1] if a>=1 else 0)))%p
        if v: ex[(a,0)]=v
    T=sadd(T,sscale(ex,(-1)%p))
    P={}
    for (a,b),v in T.items():
        if b%2: continue
        cc=b//2; ae=a-cc
        if 0<=ae<=MW: P[(ae,cc)]=(P.get((ae,cc),0)+v)%p
    mser=[2]+[0]*MW
    for order in range(1,MW+1):
        def mpow(cn,n):
            dp=[0]*(n+1); dp[0]=1
            for _ in range(cn):
                nd=[0]*(n+1)
                for i in range(n+1):
                    if dp[i]:
                        for jj in range(n+1-i): nd[i+jj]=(nd[i+jj]+dp[i]*mser[jj])%p
                dp=nd
            return dp[n]
        F0=0
        for (ae,cc),v in P.items():
            if ae<=order: F0=(F0+v*mpow(cc,order-ae))%p
        dF=0
        for (ae,cc),v in P.items():
            if ae==0 and cc>=1: dF=(dF+v*cc%p*pow(2,cc-1,p))%p
        mser[order]=(-F0)*inv(dF)%p
    ex_=[0,2]+[0]*(MW+1)
    for order in range(2,MW+2):
        def epow(pw,n):
            dp=[0]*(n+1); dp[0]=1
            for _ in range(pw):
                nd=[0]*(n+1)
                for i in range(n+1):
                    if dp[i]:
                        for jj in range(1,n+1-i): nd[i+jj]=(nd[i+jj]+dp[i]*(ex_[jj] if jj<len(ex_) else 0))%p
                dp=nd
            return dp[n]
        tot=0
        for pw in range(0,MW+1):
            if pw<len(mser) and mser[pw]: tot=(tot+mser[pw]*epow(pw,order-1))%p
        while len(ex_)<=order: ex_.append(0)
        ex_[order]=tot
    return [ex_[n+1]*inv(2)%p for n in range(1,MW+1)]
if __name__=="__main__":
    p=int(sys.argv[1]); order=int(sys.argv[2])
    A=run(p,4*order,2*order+1,order)
    print(" ".join(map(str,A)))
