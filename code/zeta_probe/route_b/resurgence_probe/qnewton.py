import mpmath as mp
mp.mp.dps=40

# eq:qdiff:  Y(qx) + q^3 Y(x/q) = (1+q^3 - 2(1-q)q^2 x^2) Y(x)
# Operator L = sigma_q + q^3 sigma_q^{-1} - (1+q^3) + 2(1-q)q^2 x^2,
# sigma_q f(x)=f(qx).  Multiply by sigma_q (=> raise to sigma^2, sigma^1, sigma^0):
#   sigma_q^2 - (1+q^3) sigma_q + q^3   + 2(1-q)q^2 (qx)^2 sigma_q  ... careful:
# Standard form: write L = a_2(x) s^2 + a_1(x) s + a_0(x), s=sigma_q, acting on Y.
# From  Y(qx)+q^3 Y(x/q) = c(x) Y(x), c(x)=1+q^3-2(1-q)q^2 x^2:
#   s Y + q^3 s^{-1} Y = c Y  -> apply s:  s^2 Y + q^3 Y = (s c)(s Y)? 
# Cleanest: keep operator with s and s^{-1}. q-Newton polygon uses orders i (power of s)
# and the x-valuations of coefficients a_i(x).
# Coefficients (in s-powers, before clearing s^{-1}):
#   order +1 (s):     1
#   order  0 :        -(1+q^3) + 2(1-q)q^2 x^2
#   order -1 (s^{-1}): q^3
# Newton polygon points (i, v_i) where v_i = x-valuation (lowest x-degree) of a_i.
# But slopes come from the SPREAD of x-degrees across orders. Use the (order, deg) hull.
# For q-difference Newton polygon (Sauloy/RSZ): plot points (i, j) for each monomial
# x^j in a_i(x), take lower convex hull; slopes = the relevant data.

pts = []
# order i=+1: coeff 1 -> monomial x^0
pts.append((1,0))
# order i=0: -(1+q^3) x^0  AND  +2(1-q)q^2 x^2
pts.append((0,0))
pts.append((0,2))
# order i=-1: q^3 x^0
pts.append((-1,0))

print("Newton points (order i, x-degree j):", sorted(set(pts)))

# Lower convex hull in (i,j). The slopes of segments = mu (q-Gevrey order s=1/|mu|).
# Shift orders so min order =0:  i'=i+1 -> orders 0,1,2
pts2=sorted(set((i+1,j) for (i,j) in pts))
print("shifted (order',deg):", pts2)

# The non-trivial x-degree (j=2) sits at order'=1 (the MIDDLE coefficient).
# Highest x-degree N=2 at order' k1=1; endpoints order'=0 (deg0) and order'=2 (deg0).
# Newton polygon for irregularity: compare the 'middle' bulge.
# Classical analogue: y'' - (large) y =0 type. The slope from (k1, N) relative to ends.
# For a 2nd-order q-diff op a2 s^2 + a1 s + a0 with deg a1 = d1, the (lower) hull slope
# between (0, v0) top-corner and the a1 vertex governs the q-Gevrey order.
print()
print("Middle coeff a_1(x) (order' k=1) has x-degree 2; ends have degree 0.")
print("This creates a slope. The q-analogue of the Newton-Ramis slope:")
print("  segment from (0,0) to (1,2): slope = +2  (rise in deg per unit order)")
print("  segment from (1,2) to (2,0): slope = -2")
print("Single nonzero slope magnitude mu=2 => formal sln q-Gevrey order s=1/mu=1/2? ")
print("BUT note: this is the polygon in (order, x-degree). The q-Gevrey order in x")
print("of the d_k series is read from d_k growth directly (below).")
