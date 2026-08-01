# OEIS packaging: u_2 coefficients + the m=0 lattice value (v2.12.9)

Raw data + verified facts ONLY. All OEIS-facing text (name, comments, replies) is to be
written personally by Vico Bonfioli, per the standing submission rules (bare-minimum
comments; no AI-drafted prose). Search OEIS for both term lists BEFORE submitting.

Both sequences derive from the Hahn-Exton q-cosine
  G(q,z) = Sum_{k>=0} (-1)^k q^(k(k-1)) z^k / Product_{i=1..2k} (1-q^i),
the function behind the published family A396406 / A396927 / A397437 / A397438 / A397439.

------------------------------------------------------------------------
## Candidate 1: u_2(q) = q^2 * z_2(q)  (second zero of the q-cosine, rescaled)

DEFINITION. z_2(q) = second-smallest positive zero in z of G(q,.); u_2 := q^2 z_2(q).
THEOREM (companion paper, thm:integrality): u_2 in 1 + q*Z[[q]] -- integer coefficients,
via the strictly convex Newton polygon of G and Hensel's lemma on the edge k' in {1,2}
of F_2(q,u) = Sum_{k'} (-1)^{k'} q^((k'-2)(k'-1)) u^{k'} / (q;q)_{2k'}.
THEOREM (companion, cor:hexagonal): u_2 = 1 - q^6 - ... ; deviation onset = 2nd hexagonal
number 6; general law: onset(u_k - 1) = k(2k-1), leading coefficient -1.

OFFSET 0. FIRST 36 TERMS:
1, 0, 0, 0, 0, 0, -1, 0, -2, 1, -4, 5, -8, 14, -21, 35, -56, 92, -149, 250, -402, 684,
-1121, 1891, -3172, 5332, -9044, 15295, -26028, 44337, -75717, 129543, -222179, 381379,
-656333, 1130409

B-FILE: bfile_u2.txt (n = 0..300, exact integers, doubly computed: integer Newton on
F_2 + cross-check against beta2_zero_lattice.py order-300 run).

Growth: |a(n)|^(1/n) -> 1/0.5545786... (radius = |q_c|, the fold point of the zero
configuration -- same radius as the z_1 branch).

Suggested crossrefs (user's choice): A396406 family; the z_1-coefficient sequence
1,-1,0,-1,1,-1,2,-2,4,-6,8,-14,21,... if/when filed -- file both together so they
cross-reference.

PARI check (first terms; user may adapt):
  N=40; q='q+O('q^N);
  G(z)=sum(k=0,10,(-1)^k*q^(k*(k-1))*z^k/prod(i=1,2*k,1-q^i));
  \\ Newton for u_2 on F_2(q,u) = q^2*G(q, u/q^2):
  u=1+O('q^N); for(j=1,9, F=sum(k=0,12,(-1)^k*q^((k-2)*(k-1))*u^k/prod(i=1,2*k,1-q^i)); \
     Fu=sum(k=1,12,(-1)^k*k*q^((k-2)*(k-1))*u^(k-1)/prod(i=1,2*k,1-q^i)); u=u-F/Fu);
  Vec(u)

------------------------------------------------------------------------
## Candidate 2: a(n) = [q^n] (-G(q,1))  (the q-cosine at z=1: the m=0 lattice value)

DEFINITION. -G(q,1) = -Sum_{k>=0} (-1)^k q^(k(k-1)) / Product_{i=1..2k} (1-q^i).
Integer coefficients (reciprocal Pochhammers are partition g.f.s).

THE LATTICE-VALUE IDENTITY (companion, prop:latticevalues; the m=0 case, verified as an
exact identity in Z[[q]] to order 300):
  (q;q^2)_oo * G(q,1) = -(q^2;q^2)_oo * Sum_{r>=0} (-1)^r q^((1+r)^2) /
                          ( (q^2;q^2)_r * (q^2;q^2)_{1+r} )
General m: G(q,q^{-2m}) = (-1)^{m+1} [(q^2;q^2)_oo/(q;q^2)_oo] *
  Sum_{r>=0} (-1)^r q^((m+1+r)^2) / ((q^2;q^2)_r (q^2;q^2)_{m+1+r}),
so ord_q G(q,q^{-2m}) = (m+1)^2 exactly (square vanishing on the lattice; this is the
identity behind the hexagonal law). The r-sum is a Hahn-Exton series of integer order
m+1 in base q^2.

OFFSET 1 (a(0)=0). FIRST 36 TERMS FROM n=0:
0, 1, 1, 1, 1, 0, 0, -1, -2, -3, -4, -5, -6, -7, -8, -8, -8, -8, -7, -6, -4, -1, 2, 6,
11, 16, 22, 29, 36, 44, 52, 60, 68, 76, 83, 90

B-FILE: bfile_negG_q1.txt (n = 0..300, exact).

Note the sign-oscillatory, slowly-varying profile (theta-sparse numerator against
partition denominators). Radius of convergence 1 (poles of 1/(q;q)_{2k} at roots of
unity; natural boundary status not established -- do not claim it).

PARI check:
  N=40; q='q+O('q^N); -sum(k=0,10,(-1)^k*q^(k*(k-1))/prod(i=1,2*k,1-q^i))

------------------------------------------------------------------------
VERIFICATION PROVENANCE: code/zeta_probe/route_b/beta2_hexagonal_law.py (identity,
exact to order 250 for m<=4 + 50-digit numeric), beta2_zero_lattice.py (u_k series),
this package's data regenerated independently in the v2.12.9 commit.

------------------------------------------------------------------------
## Candidate 3 (added v2.12.12): v_1(q) = q * w_1(q)  (first zero of the q-sine, rescaled)

DEFINITION. w_1(q) = smallest positive zero in z of the q-sine
H(q,z) = Sum_{k>=0} (-1)^k q^(k^2) (1-q) z^k / Product_{i=1..2k+1} (1-q^i); v_1 := q*w_1(q).
THEOREM (companion prop:sinelattice): v_k = q^{2k-1} w_k in 1 + q*Z[[q]] for every k
(same Newton-polygon/Hensel proof as the cosine side); onset(v_k - 1) = k(2k+1) = T_{2k}
(even-indexed triangular numbers), leading coefficient -1.
THE TRIANGULAR LAW (rem:triangular): cosine onsets T_{2k-1}, sine onsets T_{2k} -- the two
interleaved lattices switch on at every triangular number exactly once.
STABLE LAW (prop:stablelaw): both deviations stabilize to 1/(q^2;q^2)_oo^2 as k -> oo.

OFFSET 0. FIRST 36 TERMS:
1, 0, 0, -1, 0, -1, 0, -1, 1, -1, 2, -1, 4, -2, 6, -6, 9, -14, 14, -30, 28, -56, 64,
-101, 148, -188, 321, -385, 657, -844, 1310, -1887, 2648, -4132, 5567, -8810

B-FILE: bfile_v1.txt (n = 0..300, exact integers, Newton on the sine-side F with
residual identically zero).

Growth note: |a(35)|^(1/35) ~ 1.30 (radius ~ 0.77?); the sine-side radius/fold has NOT
been located -- do not state a radius. Crossref with u_2 and the z_1 sequence if filed.

PARI check:
  N=40; q='q+O('q^N);
  v=1+O('q^N); for(j=1,9, F=sum(k=0,12,(-1)^k*q^((k-1)*k)*v^k/prod(i=2,2*k+1,1-q^i)); \
     Fv=sum(k=1,12,(-1)^k*k*q^((k-1)*k)*v^(k-1)/prod(i=2,2*k+1,1-q^i)); v=v-F/Fv);
  Vec(v)
