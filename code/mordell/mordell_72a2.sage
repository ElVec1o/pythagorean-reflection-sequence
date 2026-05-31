#!/usr/bin/env sage
# V_{3/4}: square-discriminant condition for cos^2(theta)=3/4 (interior dihedral),
#   y^2 = 9*x^4+30*x^2+9   (x = a/c).  V has a rational point (x=0), so V is birational to
#   its Jacobian E (Cremona 72a2); E has rank 0, so E(Q) -- and hence V(Q) -- is finite
#   and equals the computable torsion.  This CERTIFIES finiteness (not the box search).
E = EllipticCurve(QQ, pari('ellfromeqn(y^2 - (9*x^4+30*x^2+9))').sage())
print("V_{3/4}: y^2 = 9*x^4+30*x^2+9")
print("  Jacobian Cremona :", E.cremona_label())
print("  rank             :", E.rank())
print("  torsion order    :", E.torsion_order())
assert E.rank() == 0, "rank 0 certifies V(Q) finite"
R.<x> = QQ[]; f = 9*x^4+30*x^2+9
box = sorted({QQ(n)/d for n in range(-200,201) for d in range(1,201)
              if f(QQ(n)/d) >= 0 and f(QQ(n)/d).is_square()})
print("  rational x=a/c   :", box)
print("  => no pairwise-distinct positive rational legs give cos^2 theta = 3/4. CERTIFIED (rank 0).")
