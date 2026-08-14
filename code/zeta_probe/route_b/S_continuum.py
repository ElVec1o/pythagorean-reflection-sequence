import mpmath as mp
mp.mp.dps=30
exec(open('struct_probe.py').read().split('# The forward')[0])
poles=[mp.mpf(l.split()[-1]) for l in open('poles.txt') if l.split()]

# S_c=(1-q)sum_{a>=c}q^a L_a. With L_a~b0 sin(w(1-q^a))/sin(w), and continuum u=q^a:
# S(u)=(1-q)/tau * int_0^u (b0 sin(w(1-u'))/sin(w)) du'  [since sum_{a:q^a<=u} q^a L_a ~ (1/tau)int_0^u L du']
# (1-q)/tau -> 1. int_0^u sin(w(1-u'))du' = [cos(w(1-u'))/w]_0^u = (cos(w(1-u))-cos(w))/w.
# S(u) ~ (b0/sin(w)) (cos(w(1-u))-cos(w))/w.
# Then Sigma=sum S_c q^{c-1}=(1/q)sum S_c q^c ~ (1/q)(1/tau)int_0^1 S(u)du.
# int_0^1 S(u)du = (b0/(w sin w)) int_0^1 (cos(w(1-u))-cos w)du
#   = (b0/(w sin w))[ (sin(w(1-u))*(-1)/w *(-1))... compute int_0^1 cos(w(1-u))du:
#     let t=1-u: int_0^1 cos(wt)dt = sin(w)/w.  int cos w du =cos w.
#   = (b0/(w sin w))( sin w/w - cos w ).
# So Sigma ~ (1/(q tau)) (b0/(w sin w))(sin w/w - cos w).
# Using b0~2/tau (lead), w^2=2/tau => 1/(tau)=w^2/2. So b0~ w^2. (b0~2/tau=w^2).
#   Sigma ~ (1/q) * w^2 * (b0_coeff...). Let me just plug numbers vs true.
for m in [2,4,8,16,32]:
    q=poles[m-1]; N=int(50/(1-q))
    b0,b1,t0,t1,L0,L1=raw(q,N); L=[mp.mpf(0)]+L0
    tau=-mp.log(q); w=mp.sqrt(2/tau)
    Sig_cf = (1/(q*tau))*(b0/(w*mp.sin(w)))*(mp.sin(w)/w - mp.cos(w))
    Sig_true=sum(q**c*L[c]*(1-q**c) for c in range(1,N))
    print(f'm={m}: Sig_true={float(Sig_true):.6f} Sig_continuum={float(Sig_cf):.6f}')
