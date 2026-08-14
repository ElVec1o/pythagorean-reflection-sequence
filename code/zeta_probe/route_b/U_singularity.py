import mpmath as mp
mp.mp.dps=50
u=[1,3,5,8,13,21,34,55,89,144,225,351,554,875,1345,2066,3203,4971,7574,11543,17683,27108,41067,62263,94622,143881,217101,327832,495443,749195,1127236,1697179,2554961,3848384,5777651,8679441,13031206,19574659,29338781,43997388,65932461,98849591,147969934]
v=[1,3,5,8,13,21,34,55,91,148,235,371,590,931,1451,2254,3513,5455,8418,12959,19949,30640,46905,71699,109490,166969,254047,386192,586349,889599,1347444,2039911,3084135,4661368,7035665,10617513,16002526,24117471,36303371,54649900,82171011]
L=min(len(u),len(v)); u=u[:L]; v=v[:L]
d=[v[i]-u[i] for i in range(L)]

# q* travel pole
def A(k,q): return 2*q/(1-q**(k+1))
def C(k,q): return 2*q**(k+3)/(1-q**(k+2)) - 2*q**(k+2)/(1-q**(k+1))
def Sigma(k,q,J=400):
    tot=mp.mpf(0); prod=mp.mpf(1)
    for j in range(J):
        tot+=A(k+2*j,q)*prod; prod*=C(k+2*j,q)
        if abs(prod)<mp.mpf(10)**(-60) and j>20: break
    return tot
qstar=mp.findroot(lambda q: Sigma(1,q)-1, mp.mpf('0.4494536'))
xstar=mp.sqrt(qstar)
beta=1/xstar
print("travel pole q*=",mp.nstr(qstar,16)," x*=",mp.nstr(xstar,16)," beta=1/x*=",mp.nstr(beta,16))

# Estimate growth rate of u_n, v_n, d_n via ratios and via a Domb-Sykes / Aitken on u_{n+1}/u_n.
def ratios(seq):
    return [mp.mpf(seq[i+1])/seq[i] for i in range(len(seq)-1)]
ru=ratios(u); rv=ratios(v); rd=ratios(d[8:])  # d nonzero from 8
print("\nlast ratios u:", [mp.nstr(x,8) for x in ru[-6:]])
print("last ratios v:", [mp.nstr(x,8) for x in rv[-6:]])
print("last ratios d:", [mp.nstr(x,8) for x in rd[-6:]])
print("beta (target):", mp.nstr(beta,8))

# Aitken/Richardson accel on ratios (these oscillate ~1/n). Use averaging of consecutive.
def aitken(s):
    out=[]
    for i in range(len(s)-2):
        denom=s[i+2]-2*s[i+1]+s[i]
        if denom==0: out.append(s[i+1]); continue
        out.append(s[i] - (s[i+1]-s[i])**2/denom)
    return out
au=aitken(ru); av=aitken(rv)
print("\nAitken u-ratio tail:", [mp.nstr(x,9) for x in au[-5:]])
print("Aitken v-ratio tail:", [mp.nstr(x,9) for x in av[-5:]])
# also estimate radius via root test n-th root of u_n
print("\n u_n^{1/n} tail:", [mp.nstr(mp.mpf(u[n])**(mp.mpf(1)/n),9) for n in range(len(u)-5,len(u))])
print(" beta:", mp.nstr(beta,10))
