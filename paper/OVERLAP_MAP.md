# Overlap map (R1)

Built 2026-08-22 by extracting every `\begin{theorem|proposition|lemma|corollary}`
with its `\label` from each source in `paper/journal/`. Purpose: decide the
absorb-versus-cite split for `merged_novel_paper` on data rather than impression.

## Sizes

| paper | thm | prop | lem | cor | def | total |
|---|---|---|---|---|---|---|
| `paper2` | 9 | 21 | 30 | 12 | 2 | 74 |
| `paper1` | 12 | 24 | 15 | 7 | 6 | 64 |
| **`merged_novel_paper`** | **23** | 6 | 14 | 6 | 0 | **49** |
| `paper_orthoscheme` | 7 | 1 | 8 | 6 | 1 | 23 |
| `paper4` | 5 | 5 | 4 | 5 | 2 | 21 |
| `hahn_exton_qcosine` | 5 | 7 | 2 | 3 | 0 | 17 |

`merged_novel_paper` is not a summary. With 23 theorems it is the second largest
body of top-level results in the project.

## Duplication, by identical `\label`

`merged_novel_paper` and `paper_orthoscheme` carry four results under the SAME
label:

| label | `merged_novel_paper` | `paper_orthoscheme` |
|---|---|---|
| `thm:envelope` | Envelope | The envelope is rational |
| `thm:dichotomy` | Dichotomy | Universality-deviation dichotomy |
| `thm:len6` | Length six | Length-six kernel elements are dihedral |
| `thm:rank2` | Rank-two classification | Rank-two classification |

That is half of `paper_orthoscheme`'s eight top-level results. Its unique
remainder is four: `thm:rigidity`, `thm:cd-general`, `prop:plane`, `thm:barrier`.

## Duplication elsewhere, by result name

| result | papers |
|---|---|
| differential transcendence of `g` | `hahn_exton_qcosine`, `paper2` |
| effective non-rationality | `hahn_exton_qcosine`, `paper2` |
| irreducibility of the module | `hahn_exton_qcosine`, `paper2` |
| no `q`-integrability | `hahn_exton_qcosine`, `paper2` |
| connection constant / zero product | `hahn_exton_qcosine`, `paper2` |
| difference Galois group contains `SL_2` | `hahn_exton_qcosine`, `paper2` |
| **invariance of the travel block** | **`paper1`, `paper2`** |

Five of six `hahn_exton_qcosine` results also sit in `paper2`. That paper is 17
results, so it is close to a subset.

The last row is `prop:travelinv`, which is now proved (paper2 `thm:nogap`,
`cor:localzero`). Both copies must be updated together or they will disagree on
its label.

## Recommendation, given the decision to absorb only unconditional material

1. **`paper_orthoscheme`: retire.** Four of its eight results are already in
   `merged_novel_paper` under the same label; move the remaining four
   (`thm:rigidity`, `thm:cd-general`, `prop:plane`, `thm:barrier`) across and drop
   the file. Removes 23 results and 31 pages of duplication.
2. **`hahn_exton_qcosine`: keep, cite, do not absorb.** It is nearly a subset of
   `paper2`, but its content is conditional and specialised; the clean split is for
   `paper2` to cite it rather than restate it. Delete the five restatements from
   whichever of the two is not the source of record.
3. **`paper1`, `paper2`, `paper4`: keep as technical companions.** They hold the
   conditional and machinery-heavy material `merged_novel_paper` should cite, not
   contain. Resolve the `prop:travelinv` duplication first, since its label just
   changed.
4. **Housekeeping in `merged_novel_paper`:** theorem titles carry claim labels
   ("Envelope; PROVED"). That is a working convention, not journal style (Rule 12).
   Labels belong in the status section, not in the title of every theorem.

## Method

Regenerate with the extraction in this file's git history; it is a dozen lines of
`re` over the `.tex` sources. Title matching finds paraphrases only when the
bracketed names agree, so it under-reports; the label collision above was found by
comparing labels, not names, and that is the check to repeat.
