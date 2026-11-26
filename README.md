# Stein interiors of transport twistor spaces on simple surfaces

**Hudson Headley** directed the project and maintains this release. **OpenAI Codex** (GPT-6-family agents) developed the mathematical arguments, wrote the Lean proofs, helped draft the paper, and performed the internal review. Lean’s kernel checked the formal proofs. Independent human mathematical review is pending.

**Theorem.** Let $M$ be a smooth compact oriented simple Riemannian surface. The interior of its transport twistor space is Stein. More generally, for each open set $U$ in the interior of $M$, the open unit tangent disks over $U$ form a Stein manifold with the induced transport complex structure. This answers the Steinness question posed by Jan Bohr. [Manuscript (PDF)](output/pdf/stein-transport-twistor.pdf) · [Manuscript (Markdown)](STEIN-INTERIOR.md) · [Original question, slide 11](https://www.math.uni-bonn.de/people/bohr/linz22_twistor.pdf#page=11)

**Release v1.0.2 · 26 November 2026.** Run `python3 scripts/package-stein.py` from this tag to reproduce the Zenodo source ZIP. The deposit guide gives the author metadata and the two files for Zenodo. The verification log records the checks on the release sources. [Zenodo deposit fields](submission/ZENODO.md) · [Release verification](output/verification/stein-release-extraction.txt) · [Palomar interface and remaining port](palomar/README.md)

## What Lean proves

For a simple conformal disk, Lean proves compactness of holomorphic hulls, separation of points by global holomorphic functions, and existence of local coordinates given by global holomorphic functions. The complex structure is specified by the transport equations. The metric coefficient only needs to be smooth on a neighborhood of the closed disk. For the full interior there is also a checked smooth strictly plurisubharmonic exhaustion. [Universal theorems](TransportOkaGrauert/GeneralStein.lean) · [Metric-germ theorem](TransportOkaGrauert/GermStein.lean) · [Exhaustion](TransportOkaGrauert/PhysicalSteinStrict.lean)

For an abstract surface, Lean verifies the transfer to its actual tangent disk given an isothermal chart. The manuscript uses published results for the existence of that chart and the identification with the intrinsic transport distribution. The literature review of 24 November 2026 found no earlier proof for all simple metrics. [Intrinsic transfer](TransportOkaGrauert/IntrinsicDiskStein.lean) · [Geometric identification and priority review](STEIN-FORMALIZATION.md)

## Verify the proof

Run from the repository root with Elan installed. The toolchain and manifest pin Lean 4.28.0 and mathlib.

```sh
lake exe cache get
./scripts/check-stein.sh
lake env lean ReplayProjectTogether.lean
```

The script checks the strict exhaustion, audits the transitive axiom dependencies, replays the modules through Lean’s kernel and checks the exact types of `GeneralStein.universal_chart` and `GeneralStein.universal_manifold`. The final command independently replays the project declarations together against upstream dependencies. The release source inventory covers 206 modules plus the umbrella. The axiom audit found only propositional extensionality, quotient soundness and classical choice. The combined kernel replay accepted all 4,174 logical declarations. [Acceptance test](CheckGeneralStein.lean) · [Build and check log](output/verification/stein-check.txt) · [Isolated source build](output/verification/stein-clean-build.txt) · [Independent replay log](output/verification/stein-upstream-replay.txt)

The MIT License applies to the Lean source code. The Stein manuscript is licensed under [Creative Commons Attribution 4.0 International](https://creativecommons.org/licenses/by/4.0/).

[Related research notes](research/README.md)
