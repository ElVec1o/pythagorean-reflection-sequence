import mpmath as mp, pickle, numpy as np
mp.mp.dps=50
d=pickle.load(open('/tmp/an_cache.pkl','rb')); an=d['an']; agree=d['agree']
Nrel=max(n for n in an if agree[n]>=12)
a={n:mp.mpf(an[n]) for n in an}
b=[mp.mpf(0)]+[a[n]/mp.factorial(n) for n in range(1,Nrel+1)]

# Recurrence fit -> full complex A_n; track Re(A), Im(A) = distance to R_+ separately.
print(" n :   |A|      arg     Re(A)    Im(A)=dist-to-R+")
recs=[]
for n in range(8,Nrel):
    M=mp.matrix([[b[n],b[n-1]],[b[n-1],b[n-2]]])
    rhs=mp.matrix([b[n+1],b[n]])
    try:
        sol=mp.lu_solve(M,rhs); alpha,beta=sol[0],sol[1]
        disc=alpha**2+4*beta
        for r in [(alpha+mp.sqrt(disc))/2,(alpha-mp.sqrt(disc))/2]:
            A=1/r; ar=float(mp.arg(A)*180/mp.pi)
            if 20<ar<160:
                recs.append((n,A))
                print(f" {n:2d}: {float(abs(A)):7.4f} {ar:+7.2f}  {float(A.real):7.4f}  {float(A.imag):7.4f}")
                break
    except: pass

print("\n--- Im(A) = perpendicular distance from R_+ to the (upper) singularity ---")
ims=[float(A.imag) for n,A in recs if n>=10]
res=[float(A.real) for n,A in recs if n>=10]
ns=[n for n,A in recs if n>=10]
print("Im(A) sequence:",[f"{x:.3f}" for x in ims])
print("Re(A) sequence:",[f"{x:.3f}" for x in res])
# Richardson on Im(A)
xs=np.array([1.0/n for n in ns])
for nm,arr in [("Im",ims),("Re",res)]:
    M1=np.vstack([np.ones(len(xs)),xs]).T
    c,_,_,_=np.linalg.lstsq(M1,np.array(arr),rcond=None)
    M2=np.vstack([np.ones(len(xs)),xs,xs**2]).T
    c2,_,_,_=np.linalg.lstsq(M2,np.array(arr),rcond=None)
    print(f"{nm}(A): linear->{c[0]:.4f}  quad->{c2[0]:.4f}")
