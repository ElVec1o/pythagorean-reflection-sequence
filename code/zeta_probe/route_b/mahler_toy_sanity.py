# Sanity: a Mahler function with an interior pole has poles forming a d-power orbit
# with CONSTANT log-ratio 1/d. Classic example:
#   f(z) = sum_{k>=0} z^{2^k}/(1 - z^{2^k})  ... has poles at all roots of unity (dense).
# Cleaner: take the Mahler eqn  f(z) = z/(1-z) ... no. Use:
#   f(z) - f(z^2) = z/(1-z)?  Let's just take f satisfying a0(z) f(z) = a1(z) f(z^2) + b(z)
# with a0(z)=(1 - z/c) introducing a pole at z=c, then preimages at c^{1/2}, c^{1/4},...
# Build:  (1 - z/c) f(z) - f(z^2) = 0,  f(0)=1.  Solve f(z)=prod_{k>=0} 1/(1 - z^{2^k}/c).
import mpmath as mp
mp.mp.dps=40
c=mp.mpf('0.3')  # a0(z)=1-z/c has zero at z=c
def f(z,K=60):
    p=mp.mpf(1)
    for k in range(K):
        p/=(1 - z**(2**k)/c)
    return p
# poles: where 1 - z^{2^k}/c = 0 => z^{2^k}=c => |z|=c^{1/2^k}; real positive pole rho_k=c^{1/2^k}
print("Mahler f with (1-z/c)f(z)=f(z^2), pole orbit rho_k = c^{1/2^k}:")
rhos=[c**(mp.mpf(1)/2**k) for k in range(8)]
for k,r in enumerate(rhos):
    print(f"  k={k}: rho={mp.nstr(r,12)}")
print("\nln(rho_{k+1})/ln(rho_k) (should be CONSTANT =1/d=0.5):")
for k in range(len(rhos)-1):
    print(f"  k={k}: {mp.nstr(mp.log(rhos[k+1])/mp.log(rhos[k]),12)}")
