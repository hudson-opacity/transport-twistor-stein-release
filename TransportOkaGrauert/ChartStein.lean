import TransportOkaGrauert.SimpleDiskTarget
import TransportOkaGrauert.SteinDivisor
import TransportOkaGrauert.DivisorHull
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Tactic

/-!
# A fixed statement for Steinness of the transport twistor interior

The complex structure is specified by its two Cauchy–Riemann equations in
isothermal coordinates, as in Bohr–Monard–Paternain, §2.5, equation (2.7).
Taking real derivatives in the ambient chart is legitimate on the open
domain. Ambient representatives can take arbitrary values outside it.

The three classical Stein properties used here are holomorphic convexity,
point separation, and globally defined holomorphic functions with an
invertible differential at each given point. The underlying bidisk is
second countable. The open coordinate formulation uses the existing
geodesic and Jacobi definitions of simplicity.
-/
namespace TransportOkaGrauert.ChartStein

noncomputable section
open Complex Metric Set
open scoped ContDiff ComplexConjugate
abbrev E := ℂ × ℂ
abbrev ClosedDisk := closedBall (0 : ℂ) 1
abbrev CompactBundle := ClosedDisk × ClosedDisk

def point (p : CompactBundle) : E := (p.1.val, p.2.val)

theorem continuous_point : Continuous point :=
  (continuous_subtype_val.comp continuous_fst).prodMk
    (continuous_subtype_val.comp continuous_snd)

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

/-- The claim for the full open unit disk and all open base subdomains.
This definition asserts no theorem. -/
def GeneralSimpleSurfaceStatement : Prop :=
  ∀ σ : ℂ → ℝ, SimpleDiskTarget.SimpleMetric σ →
    ∀ U : Set ℂ, IsOpen U → U ⊆ ball 0 1 → HasSteinProperties σ U

theorem continuous_tests {σ : ℂ → ℝ} {U : Set ℂ} {g : interiorOver U → ℂ}
    (hg : g ∈ tests σ U) : Continuous g := by
  obtain ⟨f, hf, heq⟩ := hg
  rw [show g = fun p => f (point p.val) from funext heq]
  exact continuous_iff_continuousAt.mpr fun p =>
    ((hf p).1.continuousAt.comp continuous_point.continuousAt).comp continuous_subtype_val.continuousAt

theorem cr_smul {σ p D} (h : SatisfiesCR σ p D) (c : ℂ) : SatisfiesCR σ p (c • D) := by
  obtain ⟨hv,hh⟩ := h
  constructor
  · simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, hv]
    ring
  · simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
    linear_combination c * hh

theorem HolAt.inv {σ f p} (hf : HolAt σ f p) (hn : f p ≠ 0) :
    HolAt σ (fun q => (f q)⁻¹) p := by
  have hd := (hasDerivAt_inv hn).comp_hasFDerivAt p (hf.1.differentiableAt (by simp)).hasFDerivAt
  exact ⟨hf.1.inv hn, hd.fderiv ▸ cr_smul hf.2 _⟩

end
end TransportOkaGrauert.ChartStein
