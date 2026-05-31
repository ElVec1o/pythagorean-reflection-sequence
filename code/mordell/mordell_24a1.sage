#!/usr/bin/env sage
# Verifies the V_{1/4} branch of Class C faithfulness (paper Thm. master-C-uncond).
# V_{1/4}: a^4 + 14 a^2 c^2 + c^4 = m^2  is the square-discriminant condition for
# cos^2(theta) = 1/4 (interior dihedral). Its Jacobian is Cremona 24a1.
E = EllipticCurve([0, -28, 0, 192, 0])    # y^2 = x(x-12)(x-16)
print("V_{1/4} curve y^2 = x(x-12)(x-16)")
print("  Cremona label :", E.cremona_label())     # 24a1
print("  conductor     :", E.conductor())          # 24
print("  rank          :", E.rank())               # 0
print("  torsion       :", E.torsion_subgroup().invariants())  # (2,4)
# Rational points t=a/c with a^4+14 a^2 c^2 + c^4 a perfect square:
R.<t> = QQ[]; f = t^4 + 14*t^2 + 1
sols = sorted({QQ(n)/d for n in range(-60,61) for d in range(1,61)
               if f(QQ(n)/d) >= 0 and f(QQ(n)/d).is_square()})
print("  rational t=a/c with f(t) square:", sols, "(all give ac=0 or a=+-c)")
assert E.rank() == 0 and sols == [-1, 0, 1]
print("  => no distinct-positive-rational legs realize cos^2 theta = 1/4. OK")
