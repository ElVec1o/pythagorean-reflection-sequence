"""
BREAK-IT Q4: Is the quantum-dilog identification of D(xi) EXACT or only leading?
Independent re-derivation. Two separate things to check:

(A) Does the IZ Gaussian integral actually equal Y3 from the q-series?  (sanity on the rep itself)
(B) Is log D(xi) = -(1/2tau) Li2-pieces + O(1) EXACT, or is the "(1/2tau)" coefficient
    only the LEADING term (so the dilog identification is asymptotic, not exact)?

Key adversarial point: the claim "D is a Faddeev quantum dilog Phi_b" is only TRUE in the
b->0 limit. Faddeev's Phi_b is a specific transcendental function; the finite-tau q-Pochhammer
(-a q^? e^{ixi}; q^2)_inf is NOT literally Phi_b -- it agrees only through the EM expansion.
So the identification is LEADING/asymptotic, and the EM remainder is exactly the open piece.
We quantify: residual after subtracting the EXACT EM integral term (the Li2) -- does it stay O(1)?
And is there a clean closed coefficient, or does each q-Poch need its OWN full EM ladder?
"""
import mpmath as mp
mp.mp.dps = 45

def poch_logsum(a, p):
    tol = mp.mpf(10)**(-(mp.mp.dps+12)); s = mp.mpc(0); ai = a
    while abs(ai) > tol:
        s += mp.log(1 - ai); ai *= p
    return s

# log of (-a e^{ixi}; q^2)_inf as a function, exact
def logD_factor(a, xi, tau):
    q = mp.e**(-tau); z = mp.e**(1j*xi)
    return poch_logsum(-a*z, q**2)

# EM leading integral term: INT_0^inf log(1+ a e^{-2tau n} z) dn = -(1/2tau) Li2(-a z)
def EM_int(a, xi, tau):
    z = mp.e**(1j*xi)
    return -mp.polylog(2, -a*z)/(2*tau)

xi = mp.mpf('1.1')
print("Q4(B): residual log(-a q^4 e^{ixi};q^2)_inf - (-1/2tau Li2(-q^4 z)), order in tau.")
print("If the dilog id were EXACT, residual would be 0. It is O(1) -> id is LEADING only.")
print(f"{'tau':>8} {'a=q^4 resid':>22} {'resid*tau':>14}")
prev=None
for tau in [mp.mpf('0.08'),mp.mpf('0.04'),mp.mpf('0.02'),mp.mpf('0.01'),mp.mpf('0.005')]:
    q=mp.e**(-tau); a=q**4
    full = logD_factor(a, xi, tau)
    lead = EM_int(a, xi, tau)
    resid = full-lead
    print(f"{float(tau):>8.4f} {mp.nstr(resid,10):>22} {mp.nstr(resid*tau,8):>14}")
print()
print("=> residual is O(1) (NOT ->0): the (1/2tau)Li2 is the LEADING coefficient only.")
print("   The q-Poch is NOT literally Faddeev Phi_b; it agrees only via the EM ladder.")
print()

# Now check: is the 1/tau-order exponent EXACT = (1/2tau)Li2, or does the SECOND q-Poch
# factor a_z=2(1-q)q ALSO contribute at 1/tau order?  CONF_leading_symbolic claims az is SMALL
# so its Li2 contributes only O(1). The verifier #3 transcript claims the OPPOSITE
# ("three independent dilog pieces, residual still O(1/tau)"). RESOLVE THIS CONTRADICTION.
print("CONTRADICTION CHECK: does the a_z=2(1-q)q factor contribute at 1/tau order?")
print("verifier#3 said 'subtracting only Li2(-e^{ixi}) leaves residue growing like 1/tau' (3 pieces)")
print("CONF_leading_symbolic said a_z is SMALL so contributes only O(1). Who is right?")
print(f"{'tau':>8} {'logD_az':>20} {'logD_az*tau':>16} {'->? finite means O(1)':>8}")
for tau in [mp.mpf('0.08'),mp.mpf('0.04'),mp.mpf('0.02'),mp.mpf('0.01'),mp.mpf('0.005')]:
    q=mp.e**(-tau); az=2*(1-q)*q
    full_az = logD_factor(az, xi, tau)
    print(f"{float(tau):>8.4f} {mp.nstr(full_az,10):>20} {mp.nstr(full_az*tau,8):>16}")
print("=> if logD_az stays O(1) (not growing ~1/tau), the a_z factor is SUBLEADING (O(1)),")
print("   so the 1/tau exponent has only TWO->effectively ONE dilog (q^4->1). Settles it.")
