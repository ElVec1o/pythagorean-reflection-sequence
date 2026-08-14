import mpmath as mp, pickle, sys
pf=pickle.load(open('/tmp/polefs.pkl','rb'))
NA=int(sys.argv[1]) if len(sys.argv)>1 else 18
# use poles with dps high enough; pick the NA+extra smallest-tau (largest m) poles
ms=sorted(pf.keys())
DPS=max(pf[m][2] for m in ms)  # work at highest available precision
mp.mp.dps=DPS
# choose the NA largest-m poles (smallest tau) for the square fit (best conditioned for high n)
ms_use=sorted(ms)[-NA:]
rows=[(mp.mpf(pf[m][0]),mp.mpf(pf[m][1])) for m in ms_use]
# direct square solve (NOT normal equations)
A=mp.matrix(NA,NA); b=mp.matrix(NA,1)
for i,(tau,f) in enumerate(rows):
    b[i,0]=f
    for n in range(1,NA+1): A[i,n-1]=tau**n
sol=mp.lu_solve(A,b)
# second set: next NA poles for agreement
ms_use2=sorted(ms)[-NA-1:-1]
rows2=[(mp.mpf(pf[m][0]),mp.mpf(pf[m][1])) for m in ms_use2]
A2=mp.matrix(NA,NA); b2=mp.matrix(NA,1)
for i,(tau,f) in enumerate(rows2):
    b2[i,0]=f
    for n in range(1,NA+1): A2[i,n-1]=tau**n
sol2=mp.lu_solve(A2,b2)
known={1:mp.mpf(2269)/1296,2:mp.mpf(507266513)/251942400,3:mp.mpf(2097873762713657)/1199951262720000}
out={}; agree={}
print(f"square fit on m={ms_use[0]}..{ms_use[-1]} (NA={NA}), DPS={DPS}")
for n in range(1,NA+1):
    x1=sol[n-1,0]; x2=sol2[n-1,0]; d=abs(x1-x2)
    ag=DPS if d==0 else max(0,-int(mp.log10(d/(abs(x1)+mp.mpf(10)**(-DPS)))))
    out[n]=mp.nstr(x1,min(45,ag+3)); agree[n]=ag
    e=f" kdiff={mp.nstr(x1-known[n],2)}" if n in known else ""
    print(f"  a_{n}={mp.nstr(x1,min(22,ag+2))}  ag~{ag}{e}")
pickle.dump({'an':out,'agree':agree},open('/tmp/an_cache.pkl','wb'))
print("saved")
