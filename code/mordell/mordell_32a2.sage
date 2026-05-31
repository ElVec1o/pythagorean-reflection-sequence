#!/usr/bin/env sage
# Verifies the V_{1/2} branch. V_{1/2}: a^4 + 6 a^2 c^2 + c^4 = k^2 is the
# square-discriminant condition for cos^2(theta) = 1/2. Jacobian is Cremona 32a2.
E = EllipticCurve([0, 0, 0, -1, 0])       # y^2 = x^3 - x
print("V_{1/2} curve y^2 = x^3 - x")
print("  Cremona label :", E.cremona_label())     # 32a2  (NOT 'E_6')
print("  conductor     :", E.conductor())          # 32
print("  rank          :", E.rank())               # 0
print("  torsion       :", E.torsion_subgroup().invariants())  # (2,2): (0,0),(+-1,0),oo
R.<t> = QQ[]; f = t^4 + 6*t^2 + 1
sols = sorted({QQ(n)/d for n in range(-60,61) for d in range(1,61)
               if f(QQ(n)/d) >= 0 and f(QQ(n)/d).is_square()})
print("  rational t=a/c with f(t) square:", sols, "(only t=0)")
assert E.rank() == 0 and sols == [0]
print("  => no distinct-positive-rational legs realize cos^2 theta = 1/2. OK")
