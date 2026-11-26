# Stein interiors of transport twistor spaces on simple surfaces

In his 2022 Linz talk, Jan Bohr asked whether the interior of the transport twistor space of every simple Riemannian surface is Stein. Bohr and Gabriel P. Paternain proved the Euclidean-domain case in Lemma 4.10 of *The Transport Oka–Grauert principle for simple surfaces*. This repository contains a proposed proof for general simple metrics and a Lean formalization of the conformal-disk result. Independent specialist review is pending. [Bohr’s question, slide 11](https://www.math.uni-bonn.de/people/bohr/linz22_twistor.pdf#page=11) · [Bohr and Paternain](https://www.numdam.org/item/10.5802/jep.231.pdf#page=25)

**Statement.** Let $M$ be a smooth compact oriented simple Riemannian surface and let $U$ be a nonempty connected open subset of its interior. The manuscript claims that the open unit tangent disks over $U$, with the induced transport complex structure, form a Stein surface. Taking $U=M^\circ$ gives the question from the talk. [Read the paper (PDF)](output/pdf/stein-transport-twistor.pdf) · [Read on GitHub](STEIN-INTERIOR.md)

## The argument

Sections 1–3 give the shortest route. For each base point $p$, the proof uses the scalar case of Bohr and Paternain’s integrating-factor theorem to construct a holomorphic function $F_p$. In the interior, its zero set is exactly the velocity disk above $p$. On the unit tangent bundle, its zeros pick out the geodesics through $p$. For $p$ outside $U$, the reciprocals $1/F_p$ keep holomorphic hulls away from the boundary. The same zero-set description confines each compact fibre of the Remmert reduction to a single velocity disk, where a connected compact analytic subset is a point. [Manuscript, §§1–3](STEIN-INTERIOR.md#1-the-question-and-the-theorem)

Sections 6–9 give a second argument for the full interior. They use the scalar Jacobi equation to construct a smooth strictly plurisubharmonic exhaustion and conclude by Grauert’s theorem. [Manuscript, §§6–9](STEIN-INTERIOR.md#6-an-intrinsic-proof-from-the-jacobi-equation)

## What Lean checks

For a simple conformal disk, Lean checks compactness of holomorphic hulls, separation of points by global holomorphic functions, and local coordinates given by pairs of global holomorphic functions over every open base subdomain. It also checks the strict exhaustion on the full interior. Given an isothermal chart, Lean transports the Stein criteria to the tangent disk. For an abstract simple surface, the manuscript invokes published results for the existence of global isothermal coordinates and the identification of the coordinate equations with the intrinsic transport distribution. [Exact theorem statements](TransportOkaGrauert/GermStein.lean) · [Transfer to the tangent disk](TransportOkaGrauert/IntrinsicDiskStein.lean) · [Geometric identification and references](STEIN-FORMALIZATION.md) · [Strict exhaustion](TransportOkaGrauert/PhysicalSteinStrict.lean)

## Contributions

Hudson Headley initiated the experiment, directed the agents, and maintains the release. OpenAI Codex agents (GPT-6 family) developed the mathematical arguments, wrote the Lean proofs, helped draft the manuscript, and performed the internal checks. [Contribution record](formalization.yaml)

**A note from Hudson.** This experiment draws on centuries of mathematics. I’m especially grateful to Jan Bohr for posing the question and to both him and Gabriel Paternain for the integrating-factor theorem that makes the first argument possible. I’m a software engineer, and I don’t have the mathematical expertise to judge independently whether the proof answers the question as intended.

To me, the mathematicians who check the argument, explain why it works, and show how it fits into the field deserve credit for that work. If the argument proves useful, a brief acknowledgment that I initiated the experiment and shared the result is all I’d ask.

## Reproduce the checks

With Elan installed, run the following commands from the repository root. The toolchain and manifest pin Lean 4.28.0 and mathlib.

```sh
lake exe cache get
./scripts/check-stein.sh
lake env lean ReplayProjectTogether.lean
```

The release audit found only propositional extensionality, quotient soundness, and classical choice. The combined kernel replay accepted 4,174 logical declarations, including both universal Stein theorems. [Acceptance test](CheckGeneralStein.lean) · [Clean build](output/verification/stein-clean-build.txt) · [Kernel replay log](output/verification/stein-upstream-replay.txt)

To reproduce the v1.0.2 source archive, run `python3 scripts/package-stein.py` from that tag. The original Lean code and scripts use the MIT license. The manuscript uses CC BY 4.0. [Release verification](output/verification/stein-release-extraction.txt) · [Code license](LICENSE) · [Manuscript license](LICENSE-MANUSCRIPT.txt) · [Related research notes](research/README.md)
