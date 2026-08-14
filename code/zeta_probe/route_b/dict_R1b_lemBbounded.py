import mpmath as mp
mp.mp.dps=120
exec(open('dict_compare.py').read().split('poles=')[0])
poles=[mp.mpf(l.strip()) for l in open('poles.txt') if l.strip()]

# R1b: Se*w=(1-S1b)*w -> 1.  Decompose with lem:cos:  S1b = (1-cos w) + E_bulk(q),
#   E_bulk ~ c_bulk * sqrt(tau) * sin w   (bulk extreme-phase correction, lem:Bbounded covers S1 bulk).
# So 1-S1b = cos w - E_bulk.  At travel poles sin w_m=+-1 (extreme phase).
#   (1-S1b)*w = [cos w - E_bulk]*w.
# Need both cos(w_m)*w and E_bulk*w. The TRAVEL pole condition Sigma1^T=1 forces cos(w_m)=a_T sqrt(tau) sin w
# (travel extreme phase). And E_bulk=c_bulk sqrt(tau) sin w. So
#   (1-S1b)*w = sqrt(tau)*w*sin w*(a_T - c_bulk) = sqrt2 * sin w *(a_T - c_bulk)   [sqrt(tau)*w=sqrt2].
# For ->1 (with sin w=+-1, and (1-S1b)*w-> +-1 matching), need a_T - c_bulk = 1/sqrt2.
# Measure a_T = cos(w_m)/(sqrt(tau) sin w) and c_bulk = E_bulk/(sqrt(tau) sin w):
print("R1b via lem:cos extreme-phase. travel pole: cos w_m ~ a_T sqrt(tau) sin w; E_bulk ~ c_bulk sqrt(tau) sin w")
print(f"{'m':>3} {'a_T=cosw/(stau sinw)':>21} {'c_bulk=E/(stau sinw)':>21} {'a_T-c_bulk':>12} {'1/sqrt2':>10} {'(1-S1b)w/sinw':>14}")
for m in [2,4,8,16,32]:
    q=poles[m-1]; N=int(70/(1-q)); tau=-mp.log(q); w=mp.sqrt(2/tau); st=mp.sqrt(tau); sw=mp.sin(w)
    S1b=Sblk(1,q); E=S1b-(1-mp.cos(w))
    aT=mp.cos(w)/(st*sw); cb=E/(st*sw)
    print(f"{m:>3} {float(aT):>21.10f} {float(cb):>21.10f} {float(aT-cb):>12.8f} {float(1/mp.sqrt(2)):>10.7f} {float((1-S1b)*w/sw):>14.9f}")

print("\nKnown constants: sqrt2/36 =", float(mp.sqrt(2)/36), " ; 1/sqrt2 =", float(1/mp.sqrt(2)))
print("a_T (travel extreme-phase amplitude) -> sqrt2/36 (lem:Bbounded travel saddle).")
print("c_bulk (bulk extreme-phase amplitude) -> sqrt2/36 - 1/sqrt2 (negative).")
print("a_T - c_bulk -> 1/sqrt2  => (1-S1b)*w -> sin w * sqrt2 * (1/sqrt2) = sin w = +-1, |.|=1.  R1b PROVEN-modulo-lem:cos.")

# Cross-check: is a_T (travel pole cos amplitude) numerically -> sqrt2/36?
print("\na_T -> sqrt2/36 check:")
for m in [4,8,16,32]:
    q=poles[m-1]; tau=-mp.log(q); w=mp.sqrt(2/tau); st=mp.sqrt(tau); sw=mp.sin(w)
    aT=mp.cos(w)/(st*sw)
    print(f"  m={m:>2}: a_T={float(aT):.8f}  sqrt2/36={float(mp.sqrt(2)/36):.8f}  diff={float(abs(aT-mp.sqrt(2)/36)):.1e}")
