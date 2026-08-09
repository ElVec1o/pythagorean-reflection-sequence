# norec

Farkas certificates for `prop:no-recurrence` of paper "extra": the sequence
u_0..u_38 (OEIS A396406) satisfies no linear recurrence over Q of order at most 19.

For each order k the system

    u_n = sum_{j=1..k} c_j u_{n-j},   n = k..38      (39-k equations, k unknowns)

is shown inconsistent by producing an integer vector w with

    w^T A = 0    and    w^T b != 0.

Any rational solution c would give w^T b = w^T (A c) = 0, a contradiction. The
witness is therefore a self-contained proof: it can be checked by integer
arithmetic alone, without redoing the linear algebra that found it.

Witnesses are found by exact rational Gaussian elimination on A^T (the left null
space of A), cleared of denominators and reduced by the gcd of their entries.
All arithmetic is exact via GMP (`rug`); there is no floating point.

## Run

    cargo build --release --offline
    ./target/release/norec

Progress and witness sizes go to stderr; the certificates go to stdout, one per
line as `(k, [w_0, ..., w_{38-k}])`. Runtime is well under a second and peak
memory is negligible.

## Output consumed by

`lean/with_mathlib/NoRecurrence.lean`, which embeds the certificates and verifies
both defining properties by kernel evaluation, then applies a Farkas lemma proved
for arbitrary integer data. All nineteen witnesses have at most 22 digits per
entry.
