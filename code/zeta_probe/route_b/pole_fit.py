import mpmath as mp
mp.mp.dps=30
exec(open('struct_probe.py').read().split('# The forward')[0])
poles=[mp.mpf(l.split()[-1]) for l in open('poles.txt') if l.split()]

print(f"{'m':>3}{'tau':>11}{'w':>9}{'cos w':>10}{'sin w':>9}{'b0*tau':>10}{'s':>10}{'J0Y0':>10}")
for m in [1,2,3,4,6,8,12,16,24,32,48,64,79]:
    q=poles[m-1]; N=int(50/(1-q))
    b0,b1,t0,t1,L0,L1=raw(q,N)
    tau=-mp.log(q); w=mp.sqrt(2/tau)
    gV=q/(1-q); s=gV*t1
    cw=mp.cos(w); sw=mp.sin(w)
    # at poles cos w ~ O(sqrt tau)? print
    print(f"{m:>3}{float(tau):>11.6f}{float(w):>9.4f}{float(cw):>10.5f}{float(sw):>9.4f}{float(b0*tau):>10.5f}{float(s):>10.6f}{float(w*cw):>10.4f}")
