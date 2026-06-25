import mpmath as mp
mp.mp.dps = 80

# Sigma(tau) = sum_{k>=0} 2 q (-2(1-q))^k q^{k^2+2k} / [ (q^2;q^2)_{k+1} (q^3;q^2)_k ]
def qpoch(a, base, n):
    p = mp.mpf(1)
    ai = mp.mpf(1)
    for i in range(n):
        p *= (1 - a * ai)
        ai *= base
    return p

def Sigma(tau):
    q = mp.e ** (-tau)
    q2 = q * q
    s = mp.mpf(0)
    term0 = 2 * q
    k = 0
    while True:
        num = term0 * (-2 * (1 - q)) ** k * q ** (k * k + 2 * k)
        den = qpoch(q2, q2, k + 1) * qpoch(q ** 3, q2, k)
        t = num / den
        s += t
        if k > 3 and abs(t) < mp.mpf(10) ** (-mp.mp.dps - 5) * (abs(s) + 1):
            break
        k += 1
        if k > 5000:
            break
    return s

# travel pole w_m: solve Sigma(tau)=1 with w=sqrt(2/tau) near (m+1/2)pi.
# Robust: Newton in w with numerical derivative, then verify |dev| small.
def F(w):
    return Sigma(2 / w ** 2) - 1
def pole_w(m):
    w = (m + mp.mpf(1) / 2) * mp.pi
    h = mp.mpf(10) ** (-20)
    for _ in range(80):
        f = F(w)
        fp = (F(w + h) - F(w - h)) / (2 * h)
        if fp == 0:
            break
        dw = f / fp
        w = w - dw
        if abs(dw) < mp.mpf(10) ** (-mp.mp.dps + 12) * (abs(w) + 1):
            break
    # sanity: dev should be O(0.01)
    dev = (m + mp.mpf(1) / 2) * mp.pi - w
    if abs(dev) > mp.mpf('0.2'):
        raise ValueError("wrong branch: dev=%s" % mp.nstr(dev, 6))
    return w

# known exact c_k (c1..c5) + we will append numeric c6.. from cks.json
import json
def load_cks():
    with open('/Users/vico/Documents/elvec1o/u5b/cks.json') as f:
        raw = json.load(f)
    out = []
    for sv in raw:
        if '/' in sv:
            a, b = sv.split('/')
            out.append(mp.mpf(int(a)) / mp.mpf(int(b)))
        else:
            out.append(mp.mpf(sv))
    return out

if __name__ == '__main__':
    import sys
    cks = load_cks()
    NC = len(cks)
    print("loaded %d c_k" % NC)
    # ----- (A) least-term: min over N of |dev - S_N| vs w, fit log(minerr) ~ -c*w -----
    # Use moderate m so that N* < NC (least term reached before we exhaust coeffs).
    ms = [2, 3, 4, 5, 6, 7]
    data = []
    print("\n# (A) least-term scaling   [dev from true pole; S_N asymptotic partial sum]")
    print(" m      w         dev         N*    min|dev-S_N*|     |t_{N*}| (smallest term)")
    for m in ms:
        try:
            w = pole_w(m)
        except Exception as e:
            print(" m=%d FAILED: %s" % (m, e)); continue
        dev = (m + mp.mpf(1) / 2) * mp.pi - w
        best = None; terms = []; S = mp.mpf(0)
        for k in range(1, NC + 1):
            t = cks[k - 1] / w ** (2 * k - 1)
            S += t
            err = abs(dev - S)
            terms.append((k, abs(t), err))
            if best is None or err < best[1]:
                best = (k, err, abs(t))
        data.append((m, w, dev, best))
        print(" %2d  %s  %s   %2d   %s   %s" %
              (m, mp.nstr(w, 9), mp.nstr(dev, 9), best[0],
               mp.nstr(best[1], 6), mp.nstr(best[2], 6)))
    # fit log(min_err) = a - c*w  via consecutive pairs (read c = -slope)
    print("\n# slope c from log(min_err) between consecutive m (min_err ~ exp(-c w)):")
    for i in range(1, len(data)):
        (m0,w0,_,b0)=data[i-1]; (m1,w1,_,b1)=data[i]
        if b0[1]>0 and b1[1]>0:
            c = -(mp.log(b1[1])-mp.log(b0[1]))/(w1-w0)
            print("   m=%d->%d  (w %s->%s)   c = %s" %
                  (m0,m1, mp.nstr(w0,6), mp.nstr(w1,6), mp.nstr(c, 10)))
    # also use smallest-term |t_{N*}| ~ exp(-c w) (more robust than the error)
    print("\n# slope c from log|t_{N*}| (smallest term) between consecutive m:")
    for i in range(1, len(data)):
        (m0,w0,_,b0)=data[i-1]; (m1,w1,_,b1)=data[i]
        if b0[2]>0 and b1[2]>0:
            c = -(mp.log(b1[2])-mp.log(b0[2]))/(w1-w0)
            print("   m=%d->%d   c = %s   (compare 2=%s, pi/sqrt2=%s, sqrt2*pi/2.. )" %
                  (m0,m1, mp.nstr(c, 10), 2, mp.nstr(mp.pi/mp.sqrt(2),8)))
    print("\n  candidates: 2.0,  pi/sqrt2=%s,  pi=%s,  sqrt2=%s"
          % (mp.nstr(mp.pi/mp.sqrt(2),9), mp.nstr(mp.pi,9), mp.nstr(mp.sqrt(2),9)))
