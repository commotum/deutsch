# Printed-form comparison

`DeutschErrata` is a small companion to the historically neutral `Deutsch` library. It records the
few original printed forms needed for a decisive comparison and derives their replacements from
the same conventions and circuits used by the main development. It does not duplicate the paper
formalization.

The mathematical changes have three roots:

1. Expanding Equation (17) with the Heisenberg convention
   \(A\mapsto U^\dagger A U\) fixes the two sine orientations in Equation (18).
   `DeutschErrata.Rotation` derives the exponential rotation and checks both printed components at
   \(\theta=\pi/2\). `DeutschErrata.Teleportation` then checks two late, mechanically propagated
   endpoints without restating the five-wire circuit.
2. Retaining the leading sign in the Figure 2 joint correlation makes different outcomes follow
   the sine-square law and the joint paper-one event follow the half-cosine-square law.
   `DeutschErrata.EPR` checks both statements on the literal four-wire record and comparison
   circuit at equal settings.
3. The second event in Equation (45) must be complementary to
   \(a(\theta_1)\lor a(\theta_2)\). `DeutschErrata.Equation45` evaluates the printed sides as
   \(1\) and \(2\) at \((1,0,1)\), then verifies the complementary partition for all eight Boolean
   triples. `DeutschErrata.Bell` records that this is the partition used by the direct
   Equation-(46) moment contradiction.

The change from \(k\) to \(n\) in the computation-basis family following Equation (3) is only an
index typo: the displayed family labels all \(n\) qubits. It has no separate mathematical theorem.

## Provenance

The original printed formulas are fixed by the repository copy of
[the paper PDF](../deutsch-2000/deutsch-2000.pdf), whose SHA-256 is
`d90c9051e2a652c22fb7ccf5a41bede5b1f4aae797cb159d36068ac525f87edb`.

Git history also retains the former transcriptions:

- verified transcription object
  `fd2e2d1^:deutsch-2000/deutsch-2000-verified.md`, SHA-256
  `02468f4b0a6b731a4f733bab928c858b6f7ddcaf6142ac952a5495b404ed785b`;
- compact original transcription object `fd2e2d1^:deutsch-2000/deutsch-2000.md`, SHA-256
  `0e16b16e9308beb01f3eb4d746951cb0a8a40971a434b1bcb71b6a03d910cb3b`.

The canonical [corrected Markdown](../deutsch-2000/deutsch-2000.md) has SHA-256
`f18273e9da7109c3be329b17b3942f0fa0b6f064904e7334befbdee66732d032`.
No build or verifier reads the sibling BQP checkout.
