# OEIS submission handoff — Class C orthoscheme family + Class B (1,1,2)

You are submitting a small family of integer sequences to the OEIS (https://oeis.org).
Everything you need is in this folder. Each `N_*.txt` file is **one submission**, with
the content already split per OEIS web-form field. Do not invent or recompute data —
paste exactly what is in the files.

The author/submitter is **Vico Bonfioli** (registered OEIS contributor; this is his
account). Use that exact spelling. The 2D flagship of this project is already published
as **A396406**, and the 5D Class C entry is now **A396927** — do not resubmit those;
only cross-reference them.

---

## HARD RULES — editor (Michel Marcus) already rejected these twice. Do NOT repeat:

1. **Name everywhere is "Vico Bonfioli"** — never "V. Bonfioli". Check the LINKS field
   especially; that is where it slipped through before. Do a find for "V. Bonfioli"
   before proposing and fix every hit.
2. **DATA must have enough terms.** A dozen terms gets rejected ("needs more terms").
   Every Class C entry here has a linear recurrence, so the DATA below is already
   extended to ~25 terms via that recurrence — paste it as-is, do not truncate. (The
   one exception is the Class B entry 5_3D_B, which has NO recurrence; depth 18 is its
   verified extent and keywords hard,more cover it.)
3. **No b-file.** Data sections are complete; a b-file the same length as DATA gets
   removed (this happened on A396406).
4. **Linear-recurrence index link + easy keyword.** Any sequence with a
   constant-coefficient linear recurrence MUST carry, in LINKS, the standard line
   `<a href="/index/Rec#order_0N">Index entries for linear recurrences with constant
   coefficients</a>, signature (...)`, and keyword `easy`. Signatures already wired in:
   4D (2,1,-1) order_03; 6D (3,0,-3) order_03; 3D-C (2) order_01; 5D=A396927 was
   (3,-1,-1) order_03. (3D-B has NO recurrence -> no such link, keep hard,more.)
   Michel asked for this on A396927; pre-supplying it avoids the round-trip.
5. After pasting, re-read the live diff once and confirm (1)-(4) before clicking
   propose. These are the things that wasted review cycles already.

---

## CRITICAL: submit on a stagger, NOT all at once

Submit **one at a time, in this order**, and **wait for each to be assigned an
A-number** (it appears the moment you click submit) before starting the next. Reason:
these are a related family; editors scrutinize batch submissions harder, and the later
entries must cross-reference the A-numbers of the earlier ones.

| Order | File | Shape | Risk | Notes |
|-------|------|-------|------|-------|
| 1 | `1_5D.txt`  | 5D orthoscheme, distinct legs | low    | **DONE — published as A396927** |
| 2 | `2_4D.txt`  | 4D orthoscheme, distinct legs | low    | submit next |
| 3 | `3_6D.txt`  | 6D orthoscheme, distinct legs | low    | submit next |
| 4 | `4_3D_C.txt`| 3D orthoscheme, distinct legs | medium | near-dup of A005010 — disclose openly |
| 5 | `5_3D_B.txt`| tetrahedron (1,1,2)           | high   | submit LAST, standalone, expect questions |

`3D-A` (cube corner, all equal legs) is **NOT submitted** — it is a duplicate of the
existing **A008137**. Do not create it.

---

## Cross-reference back-filling (important)

When you submit each new entry you will learn its A-number. After the family is in:

- In **4D, 5D, 6D, 3D-C**, replace every `Axxxxxx (<dim>D ...)` placeholder in the
  CROSSREFS field with the real A-numbers of the sibling sequences once they exist.
  On first submission, where a sibling has no number yet, just omit that one line; you
  (or the editor) can add it on a later edit. Never paste a literal `Axxxxxx`.
- All entries cross-reference **A396406** (2D) and **A008137** (3D all-equal); those
  numbers are real and final — keep them.

---

## How to submit each one (OEIS web form)

1. Log in at https://oeis.org as Vico Bonfioli.
2. Go to https://oeis.org/Submit.html (or "Contribute a new sequence").
3. Copy each labelled block from the `N_*.txt` file into the matching form box:
   - **Name** → the `%N` line (one line, no trailing period unless shown).
   - **Data** → the `%S/%T/%U` digits, comma-separated, no spaces needed.
   - **Offset** → the `%O` value (e.g. `0,2`). Do not change it; the `,2` is the
     1-based index of the first term > 1 and has been verified.
   - **Comments** → each `%C` paragraph (blank line between paragraphs).
   - **Formula** → each `%F` line.
   - **Links** → each `%H` line (keep the HTML `<a href=...>` exactly).
   - **Crossrefs** → each `%Y` line (after back-filling, see above).
   - **Keywords** → the `%K` value (comma-separated, no spaces).
   - Leave **Author** to auto-fill as Vico Bonfioli.
4. Preview, check the data renders, submit.
5. **Do NOT add a b-file.** The data sections are short and fully contain the known
   terms; a b-file the same size as the data will be rejected (this already happened on
   A396406). Only add a b-file if an editor explicitly asks for many more terms.
6. Record the assigned A-number, then move to the next file.

## Responding to editors

- Be honest and concise. The proofs and data live in the linked GitHub + Zenodo.
- For **3D-C**: if an editor notes it overlaps A005010 (9*2^n), agree — it is the
  base case and is openly flagged as A005010-reindexed in the comments. It earns its
  place as the dim-3 member of the documented family, cross-linked to the others.
- For **3D-B**: expect pushback on "is this well-defined / leg-independent?". The honest
  answer is in the comments: leg-independence is **proven only for Class C** (distinct
  legs); for Class B it is **empirical/conjectural** (matched on five leg triples). Do
  not overstate it. The tetranacci/A251704 agreement is a finite-range coincidence that
  breaks at a(14) — say so plainly.
- Never claim a closed form or growth rate for 3D-B; none is proven.
- If asked for provenance of the Class C faithfulness claim: it is the
  Niven–Conway–Jones angle-irrationality → rank-0 elliptic-curve descent argument in
  the linked manuscript (Bonfioli 2026); the descent computations are in the repo
  (`code/mordell/`).

When all five are submitted (or as far as the editors allow), report back the list of
assigned A-numbers and the status of each.
