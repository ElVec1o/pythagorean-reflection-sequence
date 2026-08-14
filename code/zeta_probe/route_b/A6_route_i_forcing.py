import mpmath as mp
def cocycle(q,N):
    x=mp.mpf(0);y=mp.mpf(1);X=mp.mpf(1);Y=mp.mpf(0);qn=mp.mpf(1)
    for n in range(1,N+1):
        qn=qn*q;q2n=qn*qn;q3n=q2n*qn
        xn=x*(1+2*q2n)-2*y*qn;yn=2*x*q3n+y*(1-2*q2n)
        Xn=X*(1+2*q2n)-2*Y*qn;Yn=2*X*q3n+Y*(1-2*q2n)
        x,y,X,Y=xn,yn,Xn,Yn
    return Y,y,X,x
poles=[mp.mpf(l.strip()) for l in open("poles.txt") if l.strip()]
# PROMPT Q for route (i): is delta=d11-dSe=O(tau^2) FORCED ALGEBRAICALLY by det=1, so the gate ORDER is
# automatic and only a crude bound on the COMMON defect is needed?
# Test the HYPOTHESIS that det=1 alone forces it. det=1 at pole: P11 Se + P12 P11 =1 => P12=1/P11-Se (exact).
# This relates P12 to P11,Se but does NOT by itself force d11=dSe; that needs the leading asymptotics
# P11~w sinw and Se~sinw/w (BOTH lem:cos-class). HOWEVER: note 1/P11 - Se = P12 is O(tau^1.5) (small).
# Write 1/P11 = Se + P12. With Se=(sinw/w)(1+dSe), 1/P11=(1/(w sinw))(1+d11)^{-1}.
#  => (1/(w sinw))(1 - d11 + ...) = (sinw/w)(1+dSe) + P12
#  multiply by w sinw:  1 - d11 + d11^2 = sin^2 w (1+dSe) + w sinw P12
#  => d11 = 1 - sin^2w - sin^2w dSe - w sinw P12 + O(d11^2)
#  => d11 = cos^2 w - sin^2 w dSe - w sinw P12 + O(tau^2)
# So d11 - dSe = cos^2 w - (1+sin^2w) dSe ... not obviously O(tau^2) from det alone.
# CONCLUSION (to verify): delta=O(tau^2) is NOT purely algebraic from det; it needs that d11 and dSe
# share leading coeff, which is a lem:cos-class asymptotic fact (BOTH P11 and Se are sin w/w-type blocks
# whose O(tau) correction is the SAME B_s-defect at the same phase). Verify the relation above numerically:
print("Test the det-derived relation d11 = cos^2w - sin^2w dSe - w sinw P12 + O(d11^2):")
print(f"{'m':>3} {'d11':>12} {'RHS(det)':>12} {'resid/tau^2':>12}")
for m in [1,2,4,8,16]:
    q=poles[m-1]; tau=-mp.log(q); w=mp.sqrt(2/tau)
    mp.mp.dps=50+int(1.3*float(w)); q=poles[m-1]; tau=-mp.log(q); w=mp.sqrt(2/tau); N=int(60/(1-q))
    P12,Se,P11,P21=cocycle(q,N); sw=mp.sin(w); cw=mp.cos(w)
    d11=P11/(w*sw)-1; dSe=Se*w/sw-1
    rhs=cw**2 - sw**2*dSe - w*sw*P12 + d11**2  # include O(d11^2) leading
    print(f"{m:>3} {float(d11):>12.7f} {float(rhs):>12.7f} {float((d11-rhs)/tau**2):>12.4f}")
    mp.mp.dps=40
print()
print("=> The relation holds (det-exact up to d11^2). It says delta=d11-dSe = cos^2w -(1+sin^2w)dSe -w sinw P12")
print("   +O(tau^2). For delta=O(tau^2) we additionally need w sinw P12 = cos^2w - 2 dSe + O(tau^2), i.e. the")
print("   LEADING of P12 must match -- that's the lem:cos-class input, NOT det alone. So route (i)'s")
print("   cancellation is a same-class asymptotic fact, not a free algebraic consequence of det=1.")
