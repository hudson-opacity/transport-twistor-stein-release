import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Integrating factors for direction-dependent matrix attenuations in the plane

Let `B(w)` take values in the square complex matrices of any fixed size. The
attenuation at a unit direction is `conj w • B w`. Its integrating factor and
inverse extend from the unit circle by exponentiating `±conj z • B w`. The
geodesic equation follows by differentiating the matrix exponential along
the single matrix direction `B w`; values at different directions need not
commute.
-/

namespace TransportOkaGrauert.FlatMatrix

open scoped ComplexConjugate Matrix.Norms.Operator ContDiff
open NormedSpace

noncomputable section

variable {n : ℕ}

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

def attenuation (B : ℂ → Mat n) (w : ℂ) : Mat n := conj w • B w

def factor (B : ℂ → Mat n) (z w : ℂ) : Mat n := exp ((-conj z) • B w)

def inverseFactor (B : ℂ → Mat n) (z w : ℂ) : Mat n := exp (conj z • B w)

/-- The exponentials are mutually inverse on the whole velocity plane. -/
theorem factor_inverses (B : ℂ → Mat n) (z w : ℂ) :
    factor B z w * inverseFactor B z w = 1 ∧ inverseFactor B z w * factor B z w = 1 := by
  unfold factor inverseFactor
  rw [neg_smul]
  let x := conj z • B w
  change exp (-x) * exp x = 1 ∧ exp x * exp (-x) = 1
  rw [← exp_add_of_commute (Commute.refl x).neg_left,
    ← exp_add_of_commute (Commute.refl x).neg_right, neg_add_cancel, add_neg_cancel, exp_zero]
  exact ⟨rfl, rfl⟩

/-- Holomorphicity of the matrix coefficient on any chosen velocity domain
passes to both the factor and its inverse. -/
theorem factors_holomorphicOn (B : ℂ → Mat n) {s : Set ℂ} (hB : DifferentiableOn ℂ B s) (z : ℂ) :
    DifferentiableOn ℂ (factor B z) s ∧ DifferentiableOn ℂ (inverseFactor B z) s := by
  have he : Differentiable ℂ (exp : Mat n → Mat n) := fun _ =>
    (exp_analytic (𝕂 := ℂ) _).differentiableAt
  exact ⟨he.comp_differentiableOn (hB.const_smul (-conj z)),
    he.comp_differentiableOn (hB.const_smul (conj z))⟩

/-- The derivative along the straight geodesic satisfies `XF + AF = 0`.
Only the value of `B` at the fixed direction occurs in this equation. -/
theorem factor_transport (B : ℂ → Mat n) (z w : ℂ) :
    HasDerivAt (fun t : ℝ => factor B (z + t * w) w)
      (-(attenuation B w * factor B z w)) 0 := by
  have h : HasDerivAt (fun t : ℝ => -conj (z + (t : ℂ) * w)) (-conj w) 0 := by
    simpa only [map_add, map_mul, Complex.conj_ofReal, Pi.neg_apply, Complex.ofRealCLM_apply,
      Complex.ofReal_one, one_mul] using
      (((Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const (conj w)).const_add (conj z)).neg
  have hh := (hasDerivAt_exp_smul_const' (B w) (-conj z)).scomp_of_eq (0 : ℝ) h (by simp)
  simpa only [Function.comp_def, factor, attenuation, neg_smul, smul_mul_assoc,
    zero_mul, add_zero] using hh

/-- The joint real smoothness needed up to the boundary of a closed disk
follows from entire dependence of the matrix profile on the direction. -/
theorem factors_smooth (B : ℂ → Mat n) (hB : Differentiable ℂ B) :
    ContDiff ℝ ∞ (fun p : ℂ × ℂ => factor B p.1 p.2) ∧
    ContDiff ℝ ∞ (fun p : ℂ × ℂ => inverseFactor B p.1 p.2) := by
  have hb : ContDiff ℝ ∞ (fun p : ℂ × ℂ => B p.2) :=
    (hB.contDiff.restrict_scalars ℝ).comp contDiff_snd
  have hc : ContDiff ℝ ∞ (fun p : ℂ × ℂ => conj p.1) :=
    Complex.conjCLE.contDiff.comp contDiff_fst
  have he : ContDiff ℝ ∞ (exp : Mat n → Mat n) :=
    contDiff_iff_contDiffAt.mpr fun _ => (exp_analytic (𝕂 := ℝ) _).contDiffAt
  exact ⟨he.comp (hc.neg.smul hb), he.comp (hc.smul hb)⟩

/-- Closed-disk version. The profile is smooth up to the velocity circle and
holomorphic inside it. The base point may range over the whole plane. -/
theorem diskMatrixIntegratingFactor (B : ℂ → Mat n)
    (hol : DifferentiableOn ℂ B (Metric.ball 0 1))
    (smooth : ContDiffOn ℝ ∞ B (Metric.closedBall 0 1)) :
    let D : Set (ℂ × ℂ) := {p | p.2 ∈ Metric.closedBall 0 1}
    ContDiffOn ℝ ∞ (fun p => factor B p.1 p.2) D ∧
    ContDiffOn ℝ ∞ (fun p => inverseFactor B p.1 p.2) D ∧
    (∀ z, DifferentiableOn ℂ (factor B z) (Metric.ball 0 1) ∧
      DifferentiableOn ℂ (inverseFactor B z) (Metric.ball 0 1)) ∧
    (∀ z w, factor B z w * inverseFactor B z w = 1 ∧ inverseFactor B z w * factor B z w = 1) ∧
    ∀ z w, HasDerivAt (fun t : ℝ => factor B (z + t * w) w)
      (-(attenuation B w * factor B z w)) 0 := by
  dsimp only
  let D : Set (ℂ × ℂ) := {p | p.2 ∈ Metric.closedBall 0 1}
  have hb : ContDiffOn ℝ ∞ (fun p : ℂ × ℂ => B p.2) D :=
    smooth.comp contDiff_snd.contDiffOn fun _ hx => hx
  have hc : ContDiffOn ℝ ∞ (fun p : ℂ × ℂ => conj p.1) D :=
    (Complex.conjCLE.contDiff.comp contDiff_fst).contDiffOn
  have he : ContDiff ℝ ∞ (exp : Mat n → Mat n) :=
    contDiff_iff_contDiffAt.mpr fun _ => (exp_analytic (𝕂 := ℝ) _).contDiffAt
  exact ⟨he.comp_contDiffOn (hc.neg.smul hb), he.comp_contDiffOn (hc.smul hb),
    factors_holomorphicOn B hol, factor_inverses B, factor_transport B⟩

/-- A holomorphic matrix profile on the plane gives a matrix integrating factor
and a holomorphic inverse in every dimension. -/
theorem flatMatrixIntegratingFactor (B : ℂ → Mat n) (hB : Differentiable ℂ B) (z : ℂ) :
    Differentiable ℂ (factor B z) ∧ Differentiable ℂ (inverseFactor B z) ∧
    (∀ w, factor B z w * inverseFactor B z w = 1 ∧ inverseFactor B z w * factor B z w = 1) ∧
    ∀ w, HasDerivAt (fun t : ℝ => factor B (z + t * w) w)
      (-(attenuation B w * factor B z w)) 0 := by
  obtain ⟨hf, hi⟩ := factors_holomorphicOn B (s := Set.univ) hB.differentiableOn z
  exact ⟨differentiableOn_univ.mp hf, differentiableOn_univ.mp hi,
    factor_inverses B z, factor_transport B z⟩

/-- Each admissible Laurent monomial gains one power when the attenuation
is multiplied by the unit velocity. -/
private theorem shift_mode (w : Circle) (k : ℤ) (hk : -1 ≤ k) :
    conj (w : ℂ) * (w : ℂ) ^ (k + 1).toNat = (w : ℂ) ^ k := by
  have hk' : 0 ≤ k + 1 := by omega
  rw [← zpow_natCast, Int.toNat_of_nonneg hk', zpow_add₀ w.coe_ne_zero, zpow_one,
    ← Circle.coe_inv_eq_conj, Circle.coe_inv]
  rw [mul_comm _ ((w : ℂ) ^ k * w), mul_assoc, mul_inv_cancel₀ w.coe_ne_zero, mul_one]

/-- Integrating factors for every position-independent matrix trigonometric
polynomial with Fourier support in the integers ≥ −1. Matrix coefficients
are unrestricted. Only the attenuation is required to be a finite sum. -/
theorem finiteModesIntegratingFactor (s : Finset ℤ) (C : ℤ → Mat n)
    (support : ∀ k ∈ s, -1 ≤ k) :
    ∃ F G : ℂ → ℂ → Mat n,
      ContDiff ℝ ∞ (fun p : ℂ × ℂ => F p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℂ × ℂ => G p.1 p.2) ∧
      (∀ z, Differentiable ℂ (F z) ∧ Differentiable ℂ (G z)) ∧
      (∀ z w, F z w * G z w = 1 ∧ G z w * F z w = 1) ∧
      ∀ z (w : Circle), HasDerivAt (fun t : ℝ => F (z + t * w) w)
        (-((∑ k ∈ s, (w : ℂ) ^ k • C k) * F z w)) 0 := by
  let B (w : ℂ) : Mat n := ∑ k ∈ s, w ^ (k + 1).toNat • C k
  have hB : Differentiable ℂ B := by
    exact Differentiable.fun_sum fun k _ =>
      (differentiable_id.pow _).smul (differentiable_const _)
  have hA (w : Circle) : attenuation B w = ∑ k ∈ s, (w : ℂ) ^ k • C k := by
    simp only [attenuation, B, Finset.smul_sum, smul_smul]
    exact Finset.sum_congr rfl fun k hk => by rw [shift_mode w k (support k hk)]
  refine ⟨factor B, inverseFactor B, (factors_smooth B hB).1, (factors_smooth B hB).2,
    fun z => ⟨(flatMatrixIntegratingFactor B hB z).1, (flatMatrixIntegratingFactor B hB z).2.1⟩,
    factor_inverses B, ?_⟩
  intro z w
  simpa only [hA w] using factor_transport B z w

end

end TransportOkaGrauert.FlatMatrix
