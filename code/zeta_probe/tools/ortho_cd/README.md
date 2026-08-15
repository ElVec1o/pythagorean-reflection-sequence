# ortho_cd

Orbit growth of the right-corner orthoscheme reflection group `W(a) <= Isom(R^n)` against the
right-angled Coxeter envelope `W_n(t) = (1+t)^{n+1}/J_{n+1}(t)`, plus the Diophantine search
behind the three quartics.

This is the certificate for every layer count, every collision depth and both Diophantine
statements quoted in `paper/journal/paper_orthoscheme.tex`.

## What it computes

For a leg tuple `a`, the `n+1` facet reflections are built directly from the legs and the image
group `rho_a(W_n)` is enumerated by breadth-first search. The chamber `O(a)` is a fundamental
domain, so the sphere sizes of the image group are the orbit counts `u_d(a)`. The first depth at
which `u_d(a) < [t^d] W_n(t)` is the collision depth `cd_n(a)`; no such depth up to the depth
run is reported as `inf`.

Arithmetic is in `F_p` at two independent 61-bit primes, and the two runs must agree. Reduction
mod `p` can only identify elements that are already equal in characteristic zero or that collide
mod `p`, so each printed `u_d` is a lower bound for the characteristic-zero count and agreement
at two primes is the check. This is the same convention as the `paper4_*` tools.

## Usage

```
cargo build --release
../runcap.sh 14000  900 target/release/ortho_cd                                  # atlas.txt
../runcap.sh 14000 5400 target/release/ortho_cd --atlas atlas_deep.txt \
                                                --no-quartics --max-ball 3000000
../runcap.sh 14000  900 target/release/ortho_cd --row "label | 1,2,3,5 | 12" --no-quartics
```

Options: `--atlas FILE`, `--row SPEC` (repeatable, suppresses the atlas), `--quartics BOUND`
(default 300), `--no-quartics`, `--max-ball N` (default 3000000), `--quiet`.

Exit status is 0 only if every expectation in the input file held at both primes and the two
primes agreed row by row; otherwise 1, with the failing lines marked `FAIL`.

## Input format

One row per line, fields separated by `|`:

```
label | legs | depth | expected layer counts u_0..u_k | expected collision depth
```

Legs are positive rationals `p` or `p/q`. The last two fields are optional; when present they
are checked, so the input files are a regression suite for the paper's tables rather than a
list of things to look at.

## The two input files

`atlas.txt` holds the tuples the paper quotes with a number attached: all thirteen rows of the
atlas table with their first six layer counts and their collision depths, the counts of the
`det Q_n` remark at `(1,1,1)`, `(1,1,1,1)` and at `n = 2`, and the two tuples of the run-length
remark. Eighteen rows, all expectations checked, under a second.

`atlas_deep.txt` holds the Class C depth ladder, one tuple with pairwise distinct legs per
dimension `3 <= n <= 10`, run until the ball cap stops it. This is the positive evidence for the
Class C faithfulness conjecture. At the cap `3000000` the attained depths are

| n | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 |
|---|---|---|---|---|---|---|---|----|
| depth | 19 | 16 | 14 | 13 | 12 | 11 | 11 | 10 |

with no deviation from the envelope anywhere. Measured cost of the whole file at two primes:
214 s wall clock, peak RSS 10964 MB. The depths are a function of the cap and change if it
changes; that is why the cap is written into the paper alongside them.

## The three quartics

The quartic search covers `1 <= x, z <= BOUND`, `x != z`, and reports two lines per form: the
quartic in the legs `(x, z)`, which is empty on the box, and the same equation read as a conic
in `X = x^2`, `Z = z^2`, which is not. The conic line also re-checks the specific point the
paper names on each conic: `(X,Z) = (2,5)` on `V_1/4`, `(3,2)` on `V_1/2`, `(5,9)` on `V_3/4`.
The contrast is the content: it is what shows that restricting to squares in the lemma is not
cosmetic. The search is a falsification attempt in the sense of Rule 3, not the proof; the proof
is the rank-0 descent recorded in the paper.
