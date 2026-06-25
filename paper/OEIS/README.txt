OEIS SUBMISSION PACKAGE — FINAL
======================================================================

7 ready-to-submit sequences with companion b-files.

UPLOAD INSTRUCTIONS
-------------------

1. Go to https://oeis.org/SubmitNew (sign in required).
2. For each sequence, copy the relevant section from the .txt file
   into the corresponding field:
     %N → "Name"
     %S/%T/%U → "Data" (the comma-separated list)
     %O → "Offset"
     %C → "Comments"
     %F → "Formula"
     %Y → "Cross-references"
     %K → "Keywords"
     %H → "Links"
     %A → "Author"

3. Upload the b-file (b_<name>.txt) in the "b-file" upload section.

FILES
-----

    Sequence                        Terms    b-file
    --------                        -----    ------
    A_2D_universal.txt              39       b_A_2D_universal.txt
    A_3D_classC.txt                 15       b_A_3D_classC.txt
    A_3D_classA.txt                 31       b_A_3D_classA.txt
    A_3D_classB.txt                 18       b_A_3D_classB.txt
    A_4D_classC.txt                 11       b_A_4D_classC.txt
    A_5D_classC.txt                 11       b_A_5D_classC.txt
    A_6D_classC.txt                  9       b_A_6D_classC.txt

LINE-WIDTH NOTES
----------------

  - Data lines (%S/%T/%U) are wrapped to ≤ 72 chars; OEIS accepts up
    to 240 chars per data line.
  - %N (name) lines are single-line, ~100-170 chars.  OEIS accepts
    %N up to ~250 chars without warning; the web form auto-wraps.
  - %C, %F, %Y, %H (text fields) are wrapped to ≤ 72 chars per line.

SUGGESTED SUBMISSION ORDER
--------------------------

1. **A_2D_universal**       (most novel, highest impact)
2. **A_3D_classC**          (clean closed form, easy)
3. **A_3D_classA**          (cube corner, period-5 + Galois)
4. **A_4D_classC**, **A_5D_classC**, **A_6D_classC** (Steinberg)
5. **A_3D_classB**          (open question, hard keyword)

After acceptance, each sequence will be assigned an A-number like
A123456.  Update the paper's reference list with the assigned numbers.

CROSS-REFERENCES
----------------

These 7 sequences form a coherent family: they should all
cross-reference each other in their %Y fields.  After upload,
the OEIS editor will help finalise the cross-references.

CONTACT
-------
   Author: Vico Bonfioli
   Email:  vico@anvilstack.com
   Paper:  github.com/elvec1o/pythagorean-reflection-sequence
