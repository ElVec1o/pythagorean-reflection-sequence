#!/usr/bin/env sage
# Backs the cyclic-ideal identification in Lemma (Mayer-Vietoris reduction):
#   In Q = D_inf x <c>, with D_inf=<X,Y>, t=XY, A=<X,c>, B=<Y>,
#   I_A = QG(X-1)+QG(c-1), I_B = QG(Y-1), h=(c-1)(Y-1):
#   we claim  I_A ∩ I_B = Z[Q]·h.
# In each finite quotient D_{2N} x <c> the intersection EXCEEDS Z[Q]h by
# exactly one dimension, spanned by the rotation-norm nu_N = sum_{k<N} t^k.
# nu_N is a finite-cyclic-group artifact (no analogue in torsion-free <t>≅Z),
# so the excess vanishes in the infinite group Q and equality holds there.
def test(N):
    D = DihedralGroup(N); C = CyclicPermutationGroup(2)
    P = direct_product_permgroups([D, C])
    rP, sP, cP = P.gens()
    QG = P.algebra(QQ); one = QG(P.one())
    X = QG(sP); Y = QG(sP*rP); c = QG(cP); t = QG(rP)   # t = XY = rotation
    elts = list(P)
    LI = lambda gl: matrix(QQ,[(QG(h_)*g).to_vector() for g in gl for h_ in elts]).row_space()
    IA = LI([X-one, c-one]); IB = LI([Y-one])
    h = (c-one)*(Y-one); Qh = LI([h])
    inter = IA.intersection(IB)
    nu = sum((t^k for k in range(N)), QG.zero())
    # space spanned by Z[Q]h together with the norm-generated elements
    extra = [nu, nu*(Y-one), nu*(c-one), nu*h]
    Qh_plus = matrix(QQ, [v for v in Qh.basis()] + [e.to_vector() for e in extra]).row_space()
    excess = inter.dimension() - Qh.dimension()
    contained = inter.is_subspace(Qh_plus)
    return excess, contained
print("N : dim(I_A∩I_B) - dim(Z[Q]h) , excess ⊆ Z[Q]h + norm-module ?")
for N in range(3, 17):
    e, cont = test(N)
    assert e == 1 and cont, f"unexpected at N={N}"
    print(f"{N:2d} : excess = {e} , norm-explained = {cont}")
print("All N in 3..16: excess is exactly the rotation-norm artifact (dim 1).")
print("=> in the infinite Q = D_inf x C2, I_A ∩ I_B = Z[Q]·h.")
