import TransportOkaGrauert.Isothermal
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Calculus.ContDiff.Defs

/-!
# A concrete open chart target for simple conformal disks

The base is the closed Euclidean unit disk with a smooth ambient conformal
factor, and the metric is `exp(2λ)(dx²+dy²)`. Unit velocities are encoded by
their Euclidean angles. The geodesic equations, scalar Jacobi equation,
Fourier coefficients, and frame transport equation are explicit below.

`chartIntegratingFactorTarget` is a proposition. This file supplies its
statement and makes no identification with an abstract manifold formulation.
-/

noncomputable section

namespace TransportOkaGrauert.SimpleDiskTarget

open Complex Metric Set
open scoped ContDiff

/-- The Euclidean Laplacian in the two coordinate directions 1 and I. -/
def laplacian (lam : ℂ → ℝ) (z : ℂ) : ℝ :=
  fderiv ℝ (fun p => fderiv ℝ lam p 1) z 1 + fderiv ℝ (fun p => fderiv ℝ lam p I) z I

/-- Gaussian curvature of the conformal chart metric. -/
def curvature (lam : ℂ → ℝ) (z : ℂ) : ℝ :=
  -Real.exp (-2 * lam z) * laplacian lam z

/-- Arclength-parametrized geodesic equations on a time interval, in a lift
of the velocity angle. Within-derivatives include one-sided derivatives at
the two endpoints of a closed segment. -/
def unitGeodesicOn (lam : ℂ → ℝ) (z : ℝ → ℂ) (θ : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ t ∈ s,
    HasDerivWithinAt z ((Real.exp (-lam (z t)) : ℂ) * (Circle.exp (θ t) : ℂ)) s t ∧
    HasDerivWithinAt θ
      (Real.exp (-lam (z t)) * Isothermal.angularDrift lam (z t) (Circle.exp (θ t))) s t

/-- Normal scalar Jacobi equation `j'' + K(z(t)) j = 0`, written as a
first-order system so it has an unambiguous endpoint interpretation. -/
def jacobiOn (lam : ℂ → ℝ) (z : ℝ → ℂ) (j dj : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ t ∈ s, HasDerivWithinAt j (dj t) s t ∧
    HasDerivWithinAt dj (-(curvature lam (z t)) * j t) s t

/-- Fixed-chart simplicity hypotheses. Every initial state, including at
the boundary, has a unit geodesic extending to points strictly outside the
disk in both time directions. The disk being retained is the component up
to its first exit in each direction. For smooth coefficients the chart
geodesic ODE has unique trajectories. -/
structure SimpleMetric (lam : ℂ → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ lam
  /-- The boundary curvature in the inward-pointing convention is
  `exp(-λ) (1 + ∂r λ)` on the unit circle. -/
  strictConvex : ∀ z ∈ sphere (0 : ℂ) 1, 0 < 1 + fderiv ℝ lam z z
  escapes : ∀ z₀ ∈ closedBall (0 : ℂ) 1, ∀ θ₀ : ℝ, ∃ a b : ℝ, ∃ z θ,
    a < 0 ∧ 0 < b ∧ z 0 = z₀ ∧ θ 0 = θ₀ ∧ unitGeodesicOn lam z θ (Icc a b) ∧
      1 < ‖z a‖ ∧ 1 < ‖z b‖
  /-- On every in-disk unit geodesic segment, two distinct zeros of a
  normal Jacobi field force that field to vanish identically on the segment. -/
  noConjugate : ∀ a b : ℝ, a < b → ∀ z θ, unitGeodesicOn lam z θ (Icc a b) →
    (∀ t ∈ Icc a b, z t ∈ closedBall 0 1) →
    ∀ j dj : ℝ → ℝ, jacobiOn lam z j dj (Icc a b) → j a = 0 → j b = 0 →
      ∀ t ∈ Icc a b, j t = 0

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ
abbrev Field (n : ℕ) := ℂ → Circle → Mat n

variable {n : ℕ}

/-- Smoothness in the base coordinates and the lifted angular coordinate,
including ambient smoothness at each point of the base boundary. -/
def SmoothToBoundary (F : Field n) : Prop :=
  ∀ z ∈ closedBall (0 : ℂ) 1, ∀ (θ : ℝ) i j,
    ContDiffAt ℝ ∞ (fun p : ℂ × ℝ => F p.1 (Circle.exp p.2) i j) (z, θ)

local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

/-- The actual normalized Haar Fourier coefficients vanish below `m`.
A frequency bound places no upper bound on the Fourier expansion. -/
def ModesFrom (m : ℤ) (F : Field n) : Prop :=
  ∀ z ∈ closedBall (0 : ℂ) 1, ∀ (i j : Fin n) (k : ℤ), k < m →
    fourierCoeff (fun θ : AddCircle (2 * Real.pi) => F z θ.toCircle i j) k = 0

/-- Invertible fiberwise holomorphic integrating factor, with its inverse
specified and the geodesic transport equation checked entrywise. -/
structure IsFrame (lam : ℂ → ℝ) (A F G : Field n) : Prop where
  smoothF : SmoothToBoundary F
  smoothG : SmoothToBoundary G
  modesF : ModesFrom 0 F
  modesG : ModesFrom 0 G
  inverses : ∀ z ∈ closedBall (0 : ℂ) 1, ∀ w : Circle,
    F z w * G z w = 1 ∧ G z w * F z w = 1
  transport : ∀ z ∈ closedBall (0 : ℂ) 1, ∀ (w : Circle) (i j : Fin n),
    Isothermal.geodesicX lam (fun p v => F p v i j) z w + (A z w * F z w) i j = 0

/-- Open formalization target, the integrating-factor version in the fixed
unit disk chart. It quantifies over every rank, every conformal factor
satisfying the geometric hypotheses, and all smooth matrix attenuations
with no Fourier modes below −1. -/
def chartIntegratingFactorTarget : Prop :=
  ∀ (lam : ℂ → ℝ), SimpleMetric lam → ∀ (n : ℕ) (A : Field n),
    SmoothToBoundary A → ModesFrom (-1) A → ∃ F G : Field n, IsFrame lam A F G

end TransportOkaGrauert.SimpleDiskTarget
