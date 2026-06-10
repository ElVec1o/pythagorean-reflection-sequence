# The arithmetic route to all-depths universality (ζ-probe)

**Idea (cross-field import).** Recast the universality conjecture for A396406 as a
question in algebraic number theory rather than group theory, and attack it with the
rational root theorem over the Gaussian integers — the same leading-coefficient
mechanism used in the classical Sanov ping-pong proof that integer matrix groups are
free.

## The reformulation

Scale coordinates by 1/a. Every element of the side-reflection group is

    w  ↦  ε·ζ^k·(w or conj(w)) + P(ζ),     ε ∈ {±1}, k ∈ Z, P ∈ Z[t^{±1}],

where ζ = ζ_T = (a+bi)/(a−bi). The data (ε, δ, k, P) is **triangle-independent**;
only the evaluation t = ζ_T depends on T. `probe.py` verifies that the count of
distinct symbolic tuples reproduces the universal sequence
1, 3, 5, 8, 13, 21, 34, 55, 89, 144, **225**, 351, … exactly (depth ≤ 18 checked),
including the depth-10 Fibonacci break.

Consequently a **shape-specific extra collision** at depth ≤ d exists iff some pair of
distinct symbolic elements with the same linear part (ε, δ, k) has difference
polynomial D = P − P′ ≠ 0 with **D(ζ_T) = 0**.

## The arithmetic screen

Write ζ_T = μ/λ in lowest terms in Z[i] (λ = (a−bi)/g). Then D(ζ_T) = 0 forces, by
the rational root theorem in Z[i] (after normalizing D to a polynomial with nonzero
constant term):

    λ | lead(D)   and   μ | const(D).

Since c := N(λ) is odd, ≥ 5, and composed only of split primes (≡ 1 mod 4) — c is the
norm of a primitive Gaussian integer — a collision is possible only if **some prime
p ≡ 1 (mod 4) divides gcd(lead D, const D)**.

## Findings (probe2/3/4, depths ≤ 16)

1. **Heights grow linearly.** max |coefficient| of P at depth d is ≈ d/2 + 1
   (measured ≤ 18). Hence an unconditional theorem candidate: *at depth d, every
   triangle with a²+b² > (d+2)² satisfies universality* — the per-depth exceptional
   set is finite and explicitly bounded. This is the first effective ALL-DEPTHS-style
   statement (universality for all sufficiently large triangles at every fixed depth).
2. **The screen annihilates almost everything.** Through depth 15: 292,023 same-class
   difference pairs; gcd(lead, const) ∈ {2, 4, 6, 8, 10}. Only 3 pairs (12 at depth
   16) contain a dangerous prime (p = 5), all of the form const·t^j·(t − 1).
3. **Exact evaluation kills all survivors.** At depth 16: 12 dangerous pairs, 12
   killed, 0 alive. So **universality through depth 16 is re-proven by pure
   arithmetic**, uniformly in T, in seconds — independently of (and much more cheaply
   than) the Lean symbolic computation that reached depth 22.
4. **Structural bonus.** P(1) is constant on every (ε, δ, k) class — verified depth
   ≤ 16 — i.e. **(t − 1) divides every same-class difference**. (Provable: t = 1 is
   the degenerate specialization; evaluation at 1 factors through a quotient
   homomorphism determined by the linear part.)

## Why this could be the road to the full conjecture

All dangerous differences seen so far factor as 2^s · t^j · (t − 1) · (unit-ish). If
one can prove the structural claim that every same-class difference factors as
(t − 1) · E with the extreme coefficients of E free of primes ≡ 1 (mod 4) — or more
modestly, that survivors are always products of cyclotomic factors times integers
whose odd part avoids split primes — then Niven's theorem (ζ_T is never a root of
unity; already the paper's Class-C workhorse) finishes all-depths universality
outright. The conjecture is thereby reduced from an infinite group-theoretic
verification to a concrete combinatorial-arithmetic invariant of the translation
module.

## Certified result (certify.py)

`certify.py D` proves universality at all depths <= D for EVERY unequal-leg
rational triangle. SHARPENED BOUND: since D(zeta_T)=0 forces the primitive
minimal polynomial Phi_T = c t^2 - e t + c to divide D in Z[t] (Gauss), c_T
divides BOTH extreme coefficients, so c_T <= 2D (not 4D^2). The candidate set
collapses (depth 30: just 16 rotation numbers, c in {5,13,17,25,29,37,41,53});
each is killed by one-sided-exact modular evaluation of the full symbolic ball
(distinct mod q => distinct in Q(i)).
Run at **D = 30** (3,336,511 ball elements, 16 candidates, ~3 min, ~2 GB RAM):
all candidates collision-free. This extends the Lean kernel-checked record
(depth 22) by eight layers; trust base is Python/NumPy modular arithmetic.
Now Theorems in the paper (S "An arithmetic effective universality theorem"):
effective bound u_d^T = u_d for all d < c_T/2, plus universality through 30.

## RESOLUTION (witness.py): the conjecture is FALSE

The wall had a tunnel — going the other way. The set of realized differences is
the pure-translation subgroup T of the symbolic group, and T is an IDEAL:
(R_x R_y R_h)^2 is a glide-reflection square = pure translation by 2(t^-1 - 1)
(the right angle makes R_xR_y a half-turn, so R_xR_yR_h is a glide along the
hypotenuse). Conjugating by rotations and multiplying:

    2(t-1) Z[t^{±1}]  ⊆  T.

An ideal contains a multiple of EVERY integer polynomial — in particular of every
shape's minimal polynomial mu_T. So  w_T = tau^c r tau^{-e} r tau^c r^{-2}
(tau = glide square, r = R_xR_h) is a nontrivial symbolic element of length
6(2c+|e|)+8 <= 24c+8 that rho_T maps to the IDENTITY. Universality is false for
every rational (indeed algebraic) shape; first deviation depth n_T satisfies

    max(31, c_T/2)  <=  n_T  <=  24 c_T + 8        (sandwich)

and rho_T is faithful on the symbolic group iff the leg ratio is TRANSCENDENTAL.
witness.py verifies the witness in exact rational arithmetic: (1,2) length 104,
(3,4) length 392, (1,3) length 116 — all map to the identity isometry while
being nonzero symbolic translations. Everything previously computed is
consistent: all deviations lie beyond depth 42. The isosceles depth-4 collapse
is the extreme case c_T = 1 of the same phenomenon.

## Realistic next steps

- Port certify.py to Rust and run at depth 38 to settle whether the published
  a(31)..a(38) (computed from the (3,4) triangle) equal the generic terms
  (open: n_{(3,4)} in [31, 392]).
- Determine T exactly (is T = 2(t-1)Z[t^{±1}]?) — would give the exact minimal
  kernel elements and sharpen the sandwich constants.
- Find n_{(1,2)} exactly (prediction: in [31, 104]).

Run: `python3 probe.py 18`, `python3 probe3.py 15`, `python3 probe4.py 16`.
