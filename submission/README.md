# Stein interiors of transport twistor spaces on simple surfaces

**Hudson Headley** · Project direction and release maintenance

**OpenAI Codex (GPT-6-family agents)** developed the mathematical arguments, wrote the Lean proof, helped draft the manuscript and performed the internal checks.

Release v1.0.2 · 26 November 2026

For every smooth simple conformal metric on the closed disk and every open subset of its interior, the transport twistor interior above that subset is Stein. The whole open disk gives the case posed by Jan Bohr. The proof establishes compactness of holomorphic hulls, separation of points by global holomorphic functions, and local holomorphic coordinates given by pairs of global functions. The conformal factor may have variable curvature of either sign. [Original question, slide 11](https://www.math.uni-bonn.de/people/bohr/linz22_twistor.pdf#page=11)

## Review the theorem

Paths below are relative to the Lean project root, which contains `lakefile.toml`.

| File | What to inspect |
| --- | --- |
| `TransportOkaGrauert/GermStein.lean` | `TransportOkaGrauert.GeneralStein.manifold_of_smooth_germ` handles a metric smooth on a neighborhood of the closed disk. |
| `TransportOkaGrauert/SimpleMetricGerm.lean` | The geometric hypotheses are strict boundary convexity, exit in both time directions and absence of conjugate points. |
| `TransportOkaGrauert/SteinTwistorCoordinates.lean` | The velocity normalization and the equivalence with the two transport differential equations. |
| `TransportOkaGrauert/SteinCriterion.lean` | The three Stein properties, expressed using holomorphic functions on the complex manifold. |
| `output/pdf/stein-transport-twistor.pdf` | The research manuscript. `STEIN-FORMALIZATION.md` explains the formal proof, external geometric inputs and literature review. |

For a compact oriented simple surface given intrinsically, the mathematical argument uses the published global isothermal parametrization and the identification of its twistor distribution with those coordinate equations. These two identifications are external to the Lean proof. [Global disk isometry](https://sigma-journal.com/2026/045/sigma26-045.pdf#page=36) · [Bohr–Paternain, Lemma 4.9](https://www.numdam.org/item/10.5802/jep.231.pdf#page=23)

## Reproduce the checks

Install elan and Git. From the extracted project root, with elan on the shell path, run:

```sh
lake exe cache get
./scripts/check-stein.sh
lake env lean ReplayProjectTogether.lean
```

The project pins Lean and mathlib v4.28.0. The first command fetches the pinned dependencies and mathlib cache. The second builds the library and checks the strict exhaustion, transitive axioms, module-by-module kernel replay and the two universal Stein theorem types. The third replays the combined project against upstream dependencies alone. The original verification logs are under `output/verification/`. The complete archive inventory is in `SHA256SUMS`.

The transitive audit examined 4,176 declarations and the combined kernel replay checked all 4,174 logical declarations. Lean’s replay omits two compiler-generated runtime recursion helpers, identified in the log. The only axiom dependencies found were propositional extensionality, classical choice and quotient soundness.

The verification logs record the 24 November 2026 local checks. Independent human mathematical review and registry verification are pending.

## Licenses

The original Lean code and supporting scripts use the MIT license. The Stein manuscript uses CC BY 4.0. See `LICENSE` and `LICENSE-MANUSCRIPT.txt`.
