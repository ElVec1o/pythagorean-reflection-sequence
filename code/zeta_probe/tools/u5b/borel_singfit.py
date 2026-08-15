import json, mpmath as mp

def _u5b_data(name, argv_index=1):
    """Locate a u5b data file.

    Search order: an explicit command-line path, then $U5B_DIR, then the directory
    holding this script.  `u5b_out.txt`, `u5b_out_m200.bak` and the `cks*.json`
    coefficient files all ship next to the scripts, so the third case is the normal
    one and no argument is needed.  Larger runs of `tools/u5b` (larger --max m) are
    not shipped; point at them with an argument or with U5B_DIR."""
    import os, sys
    if len(sys.argv) > argv_index:
        return sys.argv[argv_index]
    d = os.environ.get("U5B_DIR")
    if d:
        return os.path.join(d, name)
    here = os.path.join(os.path.dirname(os.path.abspath(__file__)), name)
    if os.path.exists(here):
        return here
    raise SystemExit(
        "error: %s not found next to this script, and neither a path argument nor\n"
        "U5B_DIR was given. Regenerate it with tools/u5b; see tools/u5b/README.md." % name)

mp.mp.dps = 40

def load(fn):
    with open(fn) as f: raw=json.load(f)
    out=[]
    for sv in raw:
        if '/' in sv:
            a,b=sv.split('/'); out.append(mp.mpf(int(a))/mp.mpf(int(b)))
        else: out.append(mp.mpf(sv))
    return out

cks = load(_u5b_data('cks.json'))
K=len(cks)
# b_n = a_n/n!  with a_{k-1}=c_k/2^{k-1}  (g(tau) Borel transform coeff)
b = [ (cks[n]/mp.mpf(2)**n)/mp.factorial(n) for n in range(K) ]   # b[n]=a_n/n!
print("Borel-tau coefficients b_n=a_n/n!  (a_n=c_{n+1}/2^n), K=%d"%K)

# Assume b_n ~ 2 Re[A xi^n] for large n  (complex-conjugate Borel sing at tau_s=1/xi).
# Fit a 2-term recurrence b_n = p b_{n-1} + q b_{n-2} on the LAST few indices (asymptotic).
# Solve least-squares / exact 2x2 using consecutive windows; report xi roots, tau_s=1/xi, rho=|tau_s|.
print("\n# 2-term recurrence fit  b_n = p b_{n-1} + q b_{n-2}  on sliding windows:")
print("#   roots xi of x^2-p x-q=0 ; tau_s=1/xi ; rho=|tau_s| ; arg(tau_s) [deg]")
for j in range(3, K):
    # use 2 eqs: indices j, j-1
    # b_j   = p b_{j-1} + q b_{j-2}
    # b_{j-1}=p b_{j-2} + q b_{j-3}
    M = mp.matrix([[b[j-1], b[j-2]],[b[j-2], b[j-3]]])
    rhs = mp.matrix([b[j], b[j-1]])
    try:
        sol = mp.lu_solve(M, rhs)
    except Exception as e:
        print("  j=%d singular"%j); continue
    p,qq = sol[0], sol[1]
    disc = p*p + 4*qq
    sq = mp.sqrt(disc)
    xi1 = (p+sq)/2; xi2=(p-sq)/2
    # nearest singularity = larger |xi| (dominant growth) -> tau_s smaller modulus
    xi = xi1 if abs(xi1)>=abs(xi2) else xi2
    if xi==0: continue
    taus = 1/xi
    rho = abs(taus)
    ang = mp.arg(taus)*180/mp.pi
    print("  j=%2d  xi=%s  tau_s=%s  rho=%s  arg=%s deg"%(j,
          mp.nstr(xi,8), mp.nstr(taus,8), mp.nstr(rho,9), mp.nstr(ang,7)))

# Compare candidate singularities tau_s (imag axis natural boundary):
print("\n# candidate natural-boundary singularities tau_s and their |.|:")
cands = {
  'pi*i (1-q^2=0,j=1)': mp.pi*1j,
  '2pi/3*i (q^3=1)': 2*mp.pi/3*1j,
  'pi/2*i (1-q^4=0,j=2)': mp.pi/2*1j,
  '2pi*i': 2*mp.pi*1j,
  '3pi/2*i': 3*mp.pi/2*1j,
}
for nm,v in cands.items():
    print("   %-24s |tau_s|=%s"%(nm, mp.nstr(abs(v),9)))

# Also a robust |tau_s| via root test on |b_n|^{1/n} with Richardson:
print("\n# |b_n|^{1/n} -> 1/rho :")
for n in range(2,K):
    print("   n=%2d |b_n|^{1/n}=%s -> rho=%s"%(n, mp.nstr(abs(b[n])**(mp.mpf(1)/n),8),
          mp.nstr(1/abs(b[n])**(mp.mpf(1)/n),8) if b[n]!=0 else 'inf'))
