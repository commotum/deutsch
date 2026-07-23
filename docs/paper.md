# Equation-by-equation paper façade

`Deutsch.Paper` is the source-shaped entry point for the paper's numbered mathematics. Importing
the umbrella
[`Deutsch/Paper.lean`](../Deutsch/Paper.lean) exposes exactly one canonical declaration for each
numbered equation:

```lean
import Deutsch.Paper

#check Deutsch.Paper.equation01
#check Deutsch.Paper.equation17
#check Deutsch.Paper.equation28
#check Deutsch.Paper.equation46
```

The names are zero-padded through `equation09` and continue as `equation10` through
`equation46`. An entry may be a definition, a theorem schema, or a theorem that bundles several
components of one displayed equation. The façade keeps the sequence and shape of the numbered
presentation visible while its definitions and proofs use the same finite-dimensional
constructions as the rest of the library.

The declarations are grouped as follows:

| Equations | Façade module | Reusable topic API |
| --- | --- | --- |
| 1–8 | `Deutsch.Paper.QuantumTheory` | `Deutsch.Foundations`, `Deutsch.Register`, `Deutsch.Descriptor`, `Deutsch.Information` |
| 9–21 | `Deutsch.Paper.Gates` | `Deutsch.Gates` |
| 22–27 | `Deutsch.Paper.EPRExperiment` | `Deutsch.EPR` |
| 28 | `Deutsch.Paper.EPRComparison` | `Deutsch.EPR` |
| 29–37 | `Deutsch.Paper.Teleportation` | `Deutsch.Teleportation` |
| 38–39 | `Deutsch.Paper.LocallyInaccessible` | `Deutsch.EPR` |
| 40–46 | `Deutsch.Paper.Bell` | `Deutsch.EPR`, `Deutsch.Bell` |

Use `Deutsch.Paper` when following or checking the numbered derivation. For downstream proofs,
prefer `import Deutsch` or the narrow topical umbrella in the last column. Those APIs expose the
underlying operators, states, circuits, probability lemmas, and general theorems without making a
new development depend on the paper's numbering. See
[Reusing the public Lean API](reuse.md) for examples and import guidance.
