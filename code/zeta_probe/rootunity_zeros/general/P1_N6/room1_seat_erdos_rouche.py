import sys, math
from flint import acb, arb, ctx

ctx.prec = 200  # ~60 digits

def e(y):
    return (2j*acb.pi()*y).exp()

TOL = 1e-40

def Bser_acb(q, Kmax=140):
    s = acb(1)
    poch = acb(1)
    aa = -2*(1-q)
    k = 1
    last_mag = None
    while k <= Kmax:
        poch *= (1-q**(2*k-1))*(1-q**(2*k))
        term = aa**k * q**(k*k) / poch
        s += term
        m = float(abs(term).upper())
        # crude tail bound: once two consecutive terms both have magnitude upper bound < tol, stop
        if last_mag is not None:
            if m < TOL and last_mag < TOL:
                pad = max(m, last_mag)*4.0  # generous pad, decay is super-geometric (q^{k^2})
                re = arb(float(s.real.mid()), float(s.real.rad()) + pad)
                im = arb(float(s.imag.mid()), float(s.imag.rad()) + pad)
                s = acb(re, im)
                return s, k
        last_mag = m
        k += 1
    return s, Kmax

def main():
    a, N = 1, 6
    z = e.__call__  # not used directly; build zeta as acb
    zeta = acb(0.5, (3**0.5)/2)  # e(1/6) = (1+i sqrt3)/2, exact-ish; refine below
    # exact: cos(pi/3)=1/2, sin(pi/3)=sqrt(3)/2
    half = acb(1)/2
    sqrt3over2 = acb(3).sqrt()/2
    zeta = half + acb(0,1)*sqrt3over2

    # approximate zero locations from mpmath run (j=4,5), refine centers
    centers = {
        4: complex(0.02732181489, 0.001017999912),
        5: complex(0.02193370833, 0.0005691659052),
    }
    for j, t0 in centers.items():
        t0c = acb(t0.real, t0.imag)
        rho = abs(t0)*0.12  # small radius disk
        nsamp = 24
        vals = []
        ok = True
        for i in range(nsamp):
            ang = 2*math.pi*i/nsamp
            t = t0c + acb(rho*math.cos(ang), rho*math.sin(ang))
            q = zeta*(-t).exp()
            Bv, kused = Bser_acb(q)
            vals.append(Bv)
        # check none of the balls contain 0 (so B != 0 on the sampled boundary points, each a rigorous ball)
        margins = []
        for Bv in vals:
            r = Bv.rad()
            m = abs(Bv).lower()  # rigorous lower bound on |B| at this point if ball excludes 0... use different approach
        # compute winding number via arg of midpoints, but bound rigorously that ball doesn't straddle branch issues:
        # require |Bv| lower bound > ball radius margin, i.e. 0 not in ball, and consecutive args differ <2pi/nsamp*2 for safety
        args = []
        safe = True
        for Bv in vals:
            re, im = Bv.real, Bv.imag
            # check zero not in the ball: |mid| - rad > 0
            mid = complex(float(re.mid()), float(im.mid()))
            rad = max(float(re.rad()), float(im.rad()))*2  # rough
            if abs(mid) <= rad*3:
                safe = False
            args.append(math.atan2(mid.imag, mid.real))
        # winding number: sum of wrapped angle differences /2pi
        total = 0.0
        for i in range(nsamp):
            d = args[(i+1) % nsamp] - args[i]
            while d > math.pi: d -= 2*math.pi
            while d < -math.pi: d += 2*math.pi
            total += d
        winding = total/(2*math.pi)
        print(f"j={j} t0={t0} rho={rho:.6g} winding={winding:.4f} safe_from_zero_on_boundary={safe} kused~{kused}")

if __name__ == '__main__':
    main()
