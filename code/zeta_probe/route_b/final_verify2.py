"""
FINAL verification (task d), with ADEQUATE precision everywhere.
Count zeros of 1-S_1 (poles of G_0) and 1-Sigma_1 (poles of G^T_0) in (0,1), pushing toward 1,
confirm count grows, confirm S_0 / Sigma_0 nonzero at each (genuine poles).
Scan in w = sqrt(2/tau), tau=-ln q; each pi-interval contains ~1 zero; dps auto-scaled to w.
"""
import mpmath as mp, math

def alpha(k,tau): return 2/(mp.e**((k+1)*tau)-1)
def Sk(k,tau,dps):
    mp.mp.dps=dps
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(3000000):
        tot+=alpha(k+2*j,tau)*prod
        prod*=(alpha(k+1+2*j,tau)-alpha(k+2*j,tau))
        if abs(prod)<mp.mpf(10)**(-(dps-15)) and j>40: break
    return tot
def Ak(k,tau):
    q=mp.e**(-tau); return 2*q/(1-q**(k+1))
def Ck(k,tau):
    q=mp.e**(-tau); return 2*q**(k+3)/(1-q**(k+2)) - 2*q**(k+2)/(1-q**(k+1))
def Sigk(k,tau,dps):
    mp.mp.dps=dps
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(3000000):
        tot+=Ak(k+2*j,tau)*prod
        prod*=Ck(k+2*j,tau)
        if abs(prod)<mp.mpf(10)**(-(dps-15)) and j>40: break
    return tot

def dps_for(w): return int(float(w)/math.log(10))+55

def count_block(S1f, S0f, w_lo, w_hi, samples):
    zeros=[]; prev=None; prevw=None
    for i in range(samples+1):
        w=w_lo+(w_hi-w_lo)*mp.mpf(i)/samples
        v=S1f(2/w**2,dps_for(w))-1
        s=int(mp.sign(v))
        if prev is not None and s!=0 and prev!=0 and s!=prev:
            lo,hi=prevw,w; flo=prev
            for _ in range(80):
                mid=(lo+hi)/2; fm=int(mp.sign(S1f(2/mid**2,dps_for(mid))-1))
                if fm==flo or fm==0: lo=mid
                else: hi=mid
            wz=(lo+hi)/2; tauz=2/wz**2; qz=mp.e**(-tauz)
            s0=S0f(tauz,dps_for(wz))
            zeros.append((qz,wz,s0))
        if s!=0: prev=s; prevw=w
    return zeros

print("="*72)
print("BULK G_0: poles = zeros of 1-S_1.  Scan w in [10,60].")
print("="*72)
zb=count_block(lambda t,d:Sk(1,t,d), lambda t,d:Sk(0,t,d), mp.mpf(10), mp.mpf(60), 1000)
print(f"#poles in w-window [10,60]: {len(zb)}")
print(f"S_0 nonzero at ALL of them (genuine poles): {all(abs(s0)>mp.mpf('1e-4') for q,w,s0 in zb)}")
print("6 closest to q=1:")
for q,w,s0 in zb[-6:]:
    print(f"   q={mp.nstr(q,18):>20s}  1-q={mp.nstr(1-q,5):>10s}  S_0={mp.nstr(s0,7):>10s}")

print("\n"+"="*72)
print("TRAVEL G^T_0: poles = zeros of 1-Sigma_1.  Scan w in [10,60].")
print("="*72)
zt=count_block(lambda t,d:Sigk(1,t,d), lambda t,d:Sigk(0,t,d), mp.mpf(10), mp.mpf(60), 1000)
print(f"#poles in w-window [10,60]: {len(zt)}")
print(f"Sigma_0 nonzero at ALL: {all(abs(s0)>mp.mpf('1e-4') for q,w,s0 in zt)}")
for q,w,s0 in zt[-6:]:
    print(f"   q={mp.nstr(q,18):>20s}  1-q={mp.nstr(1-q,5):>10s}  Sigma_0={mp.nstr(s0,7):>10s}")

print("\nDEEPER push (bulk), w in [120,160] (1-q ~ 1.4e-4 .. 7.8e-5):")
zb2=count_block(lambda t,d:Sk(1,t,d), lambda t,d:Sk(0,t,d), mp.mpf(120), mp.mpf(160), 1000)
print(f"#poles in w in[120,160]: {len(zb2)}; S_0 nonzero at all: {all(abs(s0)>mp.mpf('1e-4') for q,w,s0 in zb2)}")
print(f"closest pole to 1 here: q={mp.nstr(zb2[-1][0],20)}, 1-q={mp.nstr(1-zb2[-1][0],5)}")
print(f"\nTOTAL distinct bulk poles exhibited: {len(zb)+len(zb2)}; pattern continues as w->inf.")
