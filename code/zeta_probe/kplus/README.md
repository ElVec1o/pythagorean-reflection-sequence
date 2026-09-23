# `kplus/`: numerical check of `lem:Kplus` (merged_novel_paper)

`lem:Kplus` of `paper/journal/merged_novel_paper.tex` says that the positive
compact locus `K+` of the Gram hypersurface of `W_n` (`x_i = c_i^2` in `(0,1)`,
continuants `D_2, ..., D_n > 0`, `D_{n+1} = 0`) is exactly the set of squared
consecutive-facet cosines of `n`-orthoschemes, with the explicit inverse
`b_{k+1}/b_k = x_k D_{k-1}/D_{k+1}` (`b_i = a_i^2` the squared legs).

`src/main.rs` checks this in two ways:

- **Floating point, random samples.** For `n = 3..12`, 2000 random leg tuples
  each: the Gram matrix of the facet normals has zero entries off the path,
  `D_{n+1} = 0`, and `D_{k+1}` matches its product closed form (forward map);
  and random points of `K+` are sent to legs and back to the same Gram data
  (inverse map). It prints the worst errors. This is evidence, not a proof.
- **Exact integers.** At the Vinberg points used in the paper, for
  `n = 3..200`: all `x_i >= 1`, `D_{n+1} = 0` and `D_{n-1} != 0`.

The proof of the lemma is formalised separately in
`lean/with_mathlib/OrthoschemeGram.lean` (forward closed form, positivity, the
inverse map and injectivity up to scale), with the standard axioms only.

```bash
cargo run --release
```
