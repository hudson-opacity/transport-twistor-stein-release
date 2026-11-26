# Research notes

**AI contribution.** Hudson Headley directed these investigations. OpenAI Codex agents explored the mathematical arguments, drafted the notes, and performed internal checks. Each note identifies the earlier work it uses.

These investigations are preserved as working notes. The table records how far each formalization goes. The [release theorem](../README.md) is documented separately.

| Question | Finding and verification status | Sources |
| --- | --- | --- |
| Can Birkhoff indices jump in the interior when they vanish on the boundary? | Yes. Lean checks a rank-two counterexample on the flat disk and polynomial examples with any prescribed finite jump set there. The manuscript extends the construction to closed sets away from the boundary on simple surfaces using published scalar transport results. | [Research note](JUMP-LOCI.md) · [PDF](pdf/boundary-jumping-lines.pdf) · [Counterexample](../TransportOkaGrauert/BoundaryJump.lean) · [Polynomial family](../TransportOkaGrauert/PolynomialJumps.lean) |
| Can convex foliations recover every simple metric in Michel’s boundary rigidity conjecture? | Using Petrunin’s geometric construction, the notes give an open family of simple four-ball metrics obstructing one convex-foliation strategy. Lean checks the finite vertex obstruction. The general higher-dimensional boundary rigidity conjecture remains open. | [Investigation](MICHEL-RIGIDITY.md) · [Ten-point argument](RIGIDITY-NET.md) · [PDF](pdf/michel-boundary-rigidity.pdf) · [Lean lemma](../TransportOkaGrauert/RigidityNet.lean) |
| Is there an alternative derivation of the matrix transport Oka–Grauert principle? | Bohr and Paternain proved the general principle. Lean verifies several classes of integrating factors and a reduction of the general case to a uniform estimate. The alternative derivation and its remaining analytic formalization are documented separately. | [Published theorem](https://www.numdam.org/item/10.5802/jep.231.pdf) · [Alternative derivation and Lean coverage](ALTERNATIVE-PROOF.md) · [Conditional endpoint](../TransportOkaGrauert/NearDiagonal.lean) |
