#!/usr/bin/env sage
# Verifies the V_{3/4} branch. V_{3/4}: 9 a^4 + 30 a^2 c^2 + 9 c^4 = k^2 is the
# square-discriminant condition for cos^2(theta) = 3/4. Jacobian is Cremona 72a2.
E = EllipticCurve([0, -1500, 0, 360000, 0])   # y^2 = x(x-300)(x-1200)
print("V_{3/4} curve y^2 = x(x-300)(x-1200)")
print("  Cremona label :", E.cremona_label())     # 72a2
print("  conductor     :", E.conductor())          # 72
print("  rank          :", E.rank())               # 0
print("  torsion       :", E.torsion_subgroup().invariants())  # (2,2)
R.<t> = QQ[]; f = 9*t^4 + 30*t^2 + 9
sols = sorted({QQ(n)/d for n in range(-60,61) for d in range(1,61)
               if f(QQ(n)/d) >= 0 and f(QQ(n)/d).is_square()})
print("  rational t=a/c with f(t) square:", sols, "(only t=0)")
assert E.rank() == 0 and sols == [0]
print("  => no distinct-positive-rational legs realize cos^2 theta = 3/4. OK")
