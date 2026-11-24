module

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Steinness of the transport twistor interior of a simple surface

In global isothermal coordinates the metric is exp(2σ)|dz|² on the closed
unit disk. The velocity coordinate μ is its component in the oriented
orthonormal frame, so the velocity disk is |μ| < 1. We allow every smooth
metric germ satisfying strict boundary convexity, nontrapping, and the
absence of conjugate points. For each open base subdomain the transport
holomorphic functions have compact hulls, separate points, and furnish
local coordinates. Taking U to be the full disk gives the question Jan
Bohr posed in Linz in 2022 and the disk formulation of AIM problem 795.

Bohr–Paternain, *The Transport Oka-Grauert principle for simple surfaces*,
§4.2, equation (4.14) and Lemma 4.9 (doi:10.5802/jep.231), identify the
two coordinate equations below with the intrinsic complex structure.
The real differential of a CR coordinate pair is invertible precisely when
the pair supplies holomorphic local coordinates. The base and fibre are
second countable. The metric representative and test functions may take
arbitrary values outside their domains of use.
-/

@[expose] public section
noncomputable section
open Complex Metric Set
open scoped ContDiff

namespace SteinRegistry

namespace Isothermal
/-- The coefficient of `∂θ` inside the parentheses in (2.1),
`λ_y cos(θ) - λ_x sin(θ)`. -/
def angularDrift (lam : ℂ → ℝ) (z : ℂ) (w : Circle) : ℝ :=
  fderiv ℝ lam z I * (w : ℂ).re - fderiv ℝ lam z 1 * (w : ℂ).im
end Isothermal

namespace SimpleDiskTarget

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

/-- Fixed-chart simplicity for a coefficient smooth on an open neighborhood
of the closed disk. Its representative may be arbitrary farther outside. -/
structure SimpleMetricGerm (σ : ℂ → ℝ) : Prop where
  smooth : ∃ V : Set ℂ, IsOpen V ∧ closedBall 0 1 ⊆ V ∧ ContDiffOn ℝ ∞ σ V
  strictConvex : ∀ z ∈ sphere (0 : ℂ) 1, 0 < 1 + fderiv ℝ σ z z
  escapes : ∀ z₀ ∈ closedBall (0 : ℂ) 1, ∀ θ₀ : ℝ, ∃ a b : ℝ, ∃ z θ,
    a < 0 ∧ 0 < b ∧ z 0 = z₀ ∧ θ 0 = θ₀ ∧ unitGeodesicOn σ z θ (Icc a b) ∧
      1 < ‖z a‖ ∧ 1 < ‖z b‖
  noConjugate : ∀ a b : ℝ, a < b → ∀ z θ, unitGeodesicOn σ z θ (Icc a b) →
    (∀ t ∈ Icc a b, z t ∈ closedBall 0 1) →
    ∀ j dj : ℝ → ℝ, jacobiOn σ z j dj (Icc a b) → j a = 0 → j b = 0 →
      ∀ t ∈ Icc a b, j t = 0

end SimpleDiskTarget

namespace DivisorHull

/-- Points satisfying every modulus bound on `K` given by a test function. -/
def testHull {U : Type*} (tests : Set (U → ℂ)) (K : Set U) : Set U :=
  {x | ∀ f ∈ tests, ∀ b : ℝ, (∀ k ∈ K, ‖f k‖ ≤ b) → ‖f x‖ ≤ b}

end DivisorHull

namespace ChartStein

abbrev E := ℂ × ℂ
abbrev ClosedDisk := closedBall (0 : ℂ) 1
abbrev CompactBundle := ClosedDisk × ClosedDisk

def point (p : CompactBundle) : E := (p.1.val, p.2.val)

def interiorOver (U : Set ℂ) : Set CompactBundle :=
  {p | p.1.val ∈ U ∧ ‖p.2.val‖ < 1}

/-- Twice the horizontal operator's correction, after imposing the vertical CR
equation. The nonzero real prefactor exp(-σ) is omitted. -/
def connectionCoefficient (σ : ℂ → ℝ) (p : E) : ℂ :=
  let sx : ℂ := fderiv ℝ σ p.1 1
  let sy : ℂ := fderiv ℝ σ p.1 I
  p.2 * (p.2 ^ 2 * (sx - I * sy) - (sx + I * sy))

def SatisfiesCR (σ : ℂ → ℝ) (p : E) (D : E →L[ℝ] ℂ) : Prop :=
  D (0,I) = I * D (0,1) ∧
  p.2 ^ 2 * (D (1,0) - I * D (I,0)) + (D (1,0) + I * D (I,0)) -
    connectionCoefficient σ p * D (0,1) = 0

def HolAt (σ : ℂ → ℝ) (f : E → ℂ) (p : E) : Prop :=
  ContDiffAt ℝ ∞ f p ∧ SatisfiesCR σ p (fderiv ℝ f p)

def HolOn (σ : ℂ → ℝ) (U : Set ℂ) (f : E → ℂ) : Prop :=
  ∀ p : interiorOver U, HolAt σ f (point p.val)

def tests (σ : ℂ → ℝ) (U : Set ℂ) : Set (interiorOver U → ℂ) :=
  {g | ∃ f : E → ℂ, HolOn σ U f ∧ ∀ p, g p = f (point p.val)}

structure HasSteinProperties (σ : ℂ → ℝ) (U : Set ℂ) : Prop where
  convex : ∀ K : Set (interiorOver U), IsCompact K →
    IsCompact (DivisorHull.testHull (tests σ U) K)
  separates : ∀ p q : interiorOver U, p ≠ q →
    ∃ f : E → ℂ, HolOn σ U f ∧ f (point p.val) ≠ f (point q.val)
  coordinates : ∀ p : interiorOver U, ∃ f g : E → ℂ,
    HolOn σ U f ∧ HolOn σ U g ∧
    Function.Bijective (fderiv ℝ (fun x => (f x, g x)) (point p.val))

end ChartStein

/-- The full statement, including the geometric assumptions and the open base domain. -/
def Statement : Prop :=
  ∀ σ : ℂ → ℝ, SimpleDiskTarget.SimpleMetricGerm σ →
    ∀ U : Set ℂ, IsOpen U → U ⊆ ball (0 : ℂ) 1 → ChartStein.HasSteinProperties σ U

/-- The transport twistor interior of every smooth simple disk is Stein over every open base subdomain. -/
theorem stein_transport_twistor_interior : Statement := by
  sorry

end SteinRegistry
