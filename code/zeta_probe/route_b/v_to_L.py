import mpmath as mp
mp.mp.dps=40
poles=[mp.mpf(l.split()[-1]) for l in open('poles.txt') if l.split()]

# The v-Riccati: v_{b-1}=(v_b(1+2q2b)+2q3b)/(1-2q2b-2qb v_b).
# Linear-fractional => v_b = (a P_b + b Q_b ... ) ratio of solutions of a 2nd-order linear recursion.
# Standard: set v_b = q^b * (X_{b-1}/X_b - something). Let's FIND the linearization.
# A Riccati v_{b-1}=(A v_b + B)/(C v_b + D) linearizes via v_b = -(W_{b}... ).
# Here A=1+2q2b, B=2q3b, C=-2qb, D=1-2q2b. (note in terms of step b->b-1)
# Linearize: introduce ratio v_b = (1/(-2qb)) * (D - X_{b-1}/X_b)?? Let me instead just
# numerically find the 2nd-order linear recursion whose solution-ratio gives v.
# Substituting v_b = phi_b: the matrix [[A,B],[C,D]] acting. v_{b-1}=M.v_b (Mobius).
# Composition of Mobius = matrix product. So v = limit of product of M_b^{-1}...
# Let's just confirm v_b is the log-derivative of the SAME Bessel L-equation.
# Claim: define X_b by X_b/X_{b+1} encoding v. Test: is (1-2q2b-2qb v_b) related to L-recursion?
# Simpler: we ALREADY know t1=v0 and the local mechanism. For the rigorous note, connect
# v_1=-2/3 to cos(w)=0 via the bulk solution ratio. Let me get v_b continuum:
# In bulk, v_b ~ V(z), z=w q^b. Riccati step b->b-1 is z-> z e^{tau} (z increases by factor e^tau).
# As tau->0 this is a differential Riccati: dv/d? Let me extract V(z) numerically by overlaying
# v_b vs z for several poles -- if they collapse onto one curve V(z), it's the continuum object.
import collections
print("v_b vs z=w q^b across poles (test universal curve):")
for m in [8,16,32]:
    q=poles[m-1]; N=int(50/(1-q)); tau=-mp.log(q); w=mp.sqrt(2/tau)
    varr=[mp.mpf(0)]*(N+1)
    for b in range(N,0,-1):
        qb=q**b; q2b=qb*qb; q3b=q2b*qb
        varr[b-1]=(varr[b]*(1+2*q2b)+2*q3b)/(1-2*q2b-2*qb*varr[b])
    # sample at fixed z values
    out=[]
    for ztarget in [5.0,10.0,20.0]:
        # find b with w q^b ~ ztarget => q^b=ztarget/w => b=ln(ztarget/w)/ln q
        bb=int(mp.log(ztarget/w)/mp.log(q))
        if 0<=bb<=N:
            out.append((float(w*q**bb),float(varr[bb])))
    print(f'  m={m} w={float(w):.2f}: '+'  '.join(f'(z={z:.2f},v={v:.5f})' for z,v in out))
