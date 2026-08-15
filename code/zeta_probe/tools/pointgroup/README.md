# `pointgroup`

Orbit growth of the **point group** of the right-corner orthoscheme, against the right-angled
Coxeter envelope `W_n`.

`rho_a: W_n -> Isom(R^n)` factors through the linear part `pi: Isom(R^n) -> O(n)`. If
`pi o rho_a` is injective then `rho_a` is injective, so a faithful point group settles the
generic faithfulness problem, the ambient embedding problem and finite presentation together.
The converse fails: a deviation of the point group is not a deviation of `rho_a`.

Arithmetic is in `F_p` at two independent primes, exact for rational legs. A printed sphere
count is a lower bound for the characteristic-zero count and the envelope is an upper bound, so
agreement makes the count exact. Both primes must agree or the run exits nonzero.

## Usage

```bash
./target/release/pointgroup <legs,comma-separated> <max depth> [max ball] [budget MB]
```

`budget MB` defaults to 2500 and is the **memory guard**: before expanding each depth the tool
projects the resident bytes the next frontier and ball will need and stops cleanly if that
exceeds the budget. This machine has 24 GB with swap routinely near full, so the budget, not the
ball cap, is what keeps the search resident. Run under `../runcap.sh` with a cap above the
budget, for example `../runcap.sh 3000 1800 ./target/release/pointgroup 1,2,3 40 200000000 2000`.

## Negative control

`legs 1,2` must deviate: the `n=2` point group lies in `O(2)`, which is solvable, while `W_2`
contains a free group of rank two. It deviates at depth 3.
