import TransportOkaGrauert.NearIdentity
import Mathlib.Tactic.Module

/-! A finite difference between tA and sA gives a linear equation for a
relative gauge. Uniform control near t=s is essential: off the diagonal
there is always a singular solution of the inhomogeneous equation. -/
noncomputable section
namespace TransportOkaGrauert.MixedCorrection

open SimpleDiskTarget Isothermal Metric
open scoped Matrix.Norms.Operator
variable {n : ℕ}
local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

/-- The entrywise geodesic derivative in the chart. -/
def derivX (lam : ℂ → ℝ) (U : Field n) (z : ℂ) (v : Circle) : Mat n :=
  fun i j => geodesicX lam (fun p w => U p w i j) z v

/-- The mixed operator has distinct left and right attenuations. -/
def Solves (lam : ℂ → ℝ) (A U : Field n) (t s : ℝ) : Prop :=
  ∀ z ∈ closedBall (0 : ℂ) 1, ∀ v : Circle,
    derivX lam U z v + (t • A z v) * U z v - U z v * (s • A z v) = -A z v

def step (U : Field n) (d : ℝ) : Field n := fun z v => 1 + d • U z v

theorem derivative_step (lam : ℂ → ℝ) (U : Field n) (d : ℝ) (z : ℂ) (v : Circle) :
    derivX lam (step U d) z v = d • derivX lam U z v := by
  ext i j
  change geodesicX lam (fun p w => (1 : Mat n) i j + d • U p w i j) z v = _
  simp only [geodesicX, Fourier.flatX, vertical, fderiv_const_add, deriv_const_add]
  change _ * ((fderiv ℝ (d • (fun p => U p v i j)) z) (v : ℂ) +
    _ * deriv (fun t : ℝ => (d : ℂ) * U z (v * Circle.exp t) i j) 0) = _
  rw [fderiv_const_smul_field, deriv_const_mul_field]
  simp [derivX, geodesicX, Fourier.flatX, vertical, Complex.real_smul]
  ring

theorem linear_step (a u y : Mat n) (t s : ℝ)
    (h : y + (t • a) * u - u * (s • a) = -a) :
    (t-s) • y + (t • a) * (1 + (t-s) • u) =
      (1 + (t-s) • u) * (s • a) := by
  have hy : y = -a - (t • a) * u + u * (s • a) := by
    rw [← h]; abel
  rw [hy]
  simp only [mul_add, add_mul, mul_one, one_mul, mul_smul_comm, smul_mul_assoc,
    smul_sub, smul_add, smul_neg, smul_smul]
  module

theorem intertwines {lam : ℂ → ℝ} {A U : Field n} {t s : ℝ}
    (h : Solves lam A U t s) (z : ℂ) (hz : z ∈ closedBall 0 1) (v : Circle) :
    derivX lam (step U (t-s)) z v + (t • A z v) * step U (t-s) z v =
      step U (t-s) z v * (s • A z v) := by
  rw [derivative_step]
  exact linear_step _ _ _ t s (h z hz v)

theorem scaled_smooth {U : Field n} (hu : SmoothToBoundary U) (d : ℝ) :
    SmoothToBoundary (d • U) := fun z hz θ i j => (hu z hz θ i j).const_smul d

theorem scaled_modes {U : Field n} (hu : ModesFrom 0 U) (d : ℝ) : ModesFrom 0 (d • U) := by
  intro z hz i j k hk
  change fourierCoeff (fun θ : AddCircle (2 * Real.pi) => (d : ℂ) * U z θ.toCircle i j) k = 0
  rw [fourierCoeff.const_mul, hu z hz i j k hk, mul_zero]

/-- The homogeneous candidate F is identically zero for this particular
choice of U. Existence of some smooth solution off the diagonal carries
no near-identity information without a quantitative estimate. -/
theorem singular_step {t s : ℝ} (h : t ≠ s) :
    step (fun _ _ => (-(t-s)⁻¹) • (1 : Mat n)) (t-s) = 0 := by
  funext z v
  simp [step, smul_smul, sub_ne_zero.mpr h]

theorem singular_solves (lam : ℂ → ℝ) (A : Field n) {t s : ℝ} (h : t ≠ s) :
    Solves lam A (fun _ _ => (-(t-s)⁻¹) • (1 : Mat n)) t s := by
  intro z _ v
  have hz : derivX lam (fun _ _ => (-(t-s)⁻¹) • (1 : Mat n)) z v = 0 := by
    ext i j
    simp [derivX, geodesicX, Fourier.flatX, vertical]
  rw [hz, zero_add]
  simp only [mul_smul_comm, smul_mul_assoc, mul_one, one_mul, smul_smul, ← sub_smul]
  have hc : -(t-s)⁻¹ * t - s * -(t-s)⁻¹ = -1 := by field_simp [sub_ne_zero.mpr h]; ring
  rw [hc, neg_one_smul]

end TransportOkaGrauert.MixedCorrection
