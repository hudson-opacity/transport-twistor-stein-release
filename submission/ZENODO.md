# Zenodo deposit

Use one preprint record for the paper and its reproducible Lean source. The two files are also convenient for readers who want the paper without extracting the proof project.

| Zenodo field | Value |
| --- | --- |
| Resource type | Publication → Preprint |
| Title | Stein interiors of transport twistor spaces on simple surfaces |
| Creator | Family name **Headley**, given name **Hudson** |
| Language | English |
| Licenses | Add both MIT (original Lean code and scripts) and CC BY 4.0 (manuscript). |
| Version | 1.0.1 |
| Keywords | transport twistor spaces, simple Riemannian surfaces, Stein manifolds, geometric inverse problems, Lean 4, formal verification |
| Publication date | Actual day the record is first made public |

## Description to paste

We prove that the interior of the transport twistor space of a smooth compact oriented simple Riemannian surface is Stein. More generally, its restriction above any open subset of the interior of the base is Stein. The proof constructs holomorphic functions adapted to the geodesics through each base point and uses them to establish holomorphic convexity, point separation and global functions giving local coordinates. We also construct a strictly plurisubharmonic exhaustion of the full interior.

The accompanying Lean 4.28.0 project verifies the conformal-disk formulation. The passage from an abstract surface to this formulation uses published global isothermal coordinates and the published identification of the intrinsic transport equations. The archive contains the pinned dependency manifest, theorem statements, verification scripts and dated local verification logs. OpenAI Codex agents developed the mathematical arguments, generated the formalization, helped draft the manuscript and performed internal checks. The original Lean code and scripts are available under MIT and the manuscript under CC BY 4.0. External human review and registry verification are pending.

## Files to upload

- `output/pdf/stein-transport-twistor.pdf`
- `output/submission/stein-transport-twistor-lean.zip`

Use the DOI for this specific version when corresponding about the checked proof. Zenodo can reserve that DOI in a draft and registers it when the record is published. The archived Lean environment is pinned in the source ZIP. A future Palomar entry can be linked from the record after registry verification. [Zenodo upload guide](https://help.zenodo.org/docs/deposit/create-new-upload/) · [Reserving a DOI](https://help.zenodo.org/docs/deposit/describe-records/reserve-doi/) · [Mixed-license deposits](https://help.zenodo.org/docs/deposit/describe-records/licenses/)

**Version 1.0.1 source ZIP SHA-256** `2ca95684289c492fc18dda2d92b781962265efa6782716b03865a04cac2d349c`
