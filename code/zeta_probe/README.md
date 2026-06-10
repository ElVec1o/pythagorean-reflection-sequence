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

## Realistic next steps

- Prove the P(1)-invariance lemma (easy induction) and the linear height bound
  (easy induction) → publishable effective-universality theorem as-is.
- Port the screen to Rust and push the per-depth certified universality beyond the
  Lean depth-22 record (ball growth ~1.5^d; depth ~26–30 looks feasible on 24 GB).
- Hunt for a proof of the "no split prime divides both extremes" invariant; this is
  the full conjecture's crux.

Honest status: items 1–4 are computational findings plus elementary number theory;
nothing here proves the all-depths conjecture yet. But it converts it into a finite,
attackable arithmetic question and yields new effective theorems immediately.

Run: `python3 probe.py 18`, `python3 probe3.py 15`, `python3 probe4.py 16`.
