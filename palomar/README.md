# Palomar statement and proof interface

The proposed registry theorem is `SteinRegistry.stein_transport_twistor_interior`. For every simple metric smooth on a collar of the closed disk and every open base subdomain, it asserts compact holomorphic hulls, separation by global holomorphic functions, and local coordinates supplied by global holomorphic functions for the physical transport equations. Its standalone statement spells out the geodesic and Jacobi equations, strict boundary convexity, both escape directions, and the two equations for holomorphicity. [Challenge](Challenge.lean) · [Geometric correspondence and scope](../STEIN-FORMALIZATION.md)

The solution transfers the stated simplicity hypotheses to the existing formalization. It applies `GeneralStein.chart_of_smooth_germ` and returns its three conclusions. The original proof also constructs the complex manifold atlas. This Comparator configuration selects the chart theorem. [Solution](Solution.lean) · [Verified implementation](../TransportOkaGrauert/GermStein.lean) · [Comparator configuration](comparator.json)

## Original toolchain check

Run `./palomar/check-interface.sh` after installing this repository’s pinned dependencies. The script builds the proof dependency, checks the standalone Challenge, then checks the Solution separately. The original library uses Lean 4.28 legacy modules, so the script translates only the header of its temporary copy of Solution to legacy syntax. The proof body is preserved verbatim. The separate RegistryDefinitions module lets the Solution use exactly the definitions in the Challenge, without importing its deliberate proof placeholder. The local audit compares the target declaration type and the compiled project-local definitions and constructors it uses, and traverses the axioms of the proved theorem. [Check script](check-interface.sh) · [Local comparison](CheckInterface.lean)

The 24 November 2026 local run passed. [Result and source hashes](verification.txt)

## Registry compatibility

As checked 24 November 2026, Palomar requires Lean v4.35.0-rc2 or newer and the module header throughout the source repository. This proof snapshot uses Lean 4.28.0. A trial on 4.28 caught public definitions depending on private helpers in two modules, `FourierDecay.coeff` and `Isothermal.driftUp`/`driftDown`. A full port must resolve visibility and library API differences and pass the registry Comparator and independent checkers on the supported toolchain. [Supported toolchain](https://github.com/PalomarRegistry/PalomarSubmission/blob/main/toolchains.json) · [Palomar submission guide](https://palomar-registry.org/how-to-submit)

For the port, configure Lake to expose `Challenge`, `Solution` and `RegistryDefinitions` from this directory alongside the substantive proof library. Place the Comparator JSON in the selected Lake project or enter its relative path in the form. Palomar requires a public GitHub repository, its full commit hash, matching root licensing and formalization metadata, and authenticated submitter access. Its verifier and automated editorial review determine eligibility for registration. [Registry policy](https://palomar-registry.org/about.html)
