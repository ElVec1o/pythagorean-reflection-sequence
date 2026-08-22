"""Standalone OEIS PROG candidate for A_2D_universal.
Computes a(0)..a(d_max) by BFS on the side-reflection group of a right
triangle with positive unequal rational legs, using exact rational
arithmetic. Any right triangle with unequal legs matches the universal
sequence through depth 32, so for d_max <= 32 the choice of (a,b) with
a != b is immaterial; we use (a, b) = (1, 2). Beyond that the choice does
matter: (1,2) first deviates at depth 33, giving 3848354 against the
universal 3848384 (see reproduce/deviation_1_2.py)."""
from fractions import Fraction

def universal_right_triangle_sequence(d_max=20):
    O, I = Fraction(0), Fraction(1)
    # Right triangle with legs a=1, b=2, right angle at V0
    V = [(O, O), (I, O), (O, I + I)]
    sides = [(0, 1), (1, 2), (2, 0)]  # three edges

    def reflection_across(p0, p1):
        dx, dy = p1[0] - p0[0], p1[1] - p0[1]
        L = dx * dx + dy * dy
        a = (dx * dx - dy * dy) / L
        b = 2 * dx * dy / L
        d = -a
        tx = (1 - a) * p0[0] - b * p0[1]
        ty = -b * p0[0] + (1 - d) * p0[1]
        return (a, b, b, d, tx, ty)

    def compose(M, N):
        a1, b1, c1, d1, tx1, ty1 = M
        a2, b2, c2, d2, tx2, ty2 = N
        return (
            a1*a2 + b1*c2, a1*b2 + b1*d2,
            c1*a2 + d1*c2, c1*b2 + d1*d2,
            a1*tx2 + b1*ty2 + tx1,
            c1*tx2 + d1*ty2 + ty1,
        )

    gens = [reflection_across(V[i], V[j]) for i, j in sides]
    identity = (I, O, O, I, O, O)
    seen = {identity}
    frontier = {identity}
    sequence = [1]
    for _ in range(d_max):
        new_layer = set()
        for M in frontier:
            for g in gens:
                N = compose(g, M)
                if N not in seen:
                    new_layer.add(N)
                    seen.add(N)
        sequence.append(len(new_layer))
        frontier = new_layer
    return sequence

if __name__ == "__main__":
    print(universal_right_triangle_sequence(15))
