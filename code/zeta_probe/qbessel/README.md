# Scripts behind paper2 §sec:fredholmdet

These are floating-point checks run at 40–90 digits with mpmath. They are not interval certificates.

- `c1_verify.py`, `c1_verify2.py`:
  - checks that the travel poles are zeros of J^(3)_{-1/2}(Z;q^2) at q_1..q_10;
  - counts the zeros below z*;
  - evaluates B'(q_m).
- `c1_verify2.out`: the saved output. The q_10 row there is correct. An earlier run's findroot returned q_9 for that row by mistake; that output was not kept.
- `c1_complex*.py`: exploratory computations of the complex zeros.
