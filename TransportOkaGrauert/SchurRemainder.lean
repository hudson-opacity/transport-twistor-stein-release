import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-! # Near-diagonal estimates for the remainder of the normal operator

The gradient of a bounded smooth polar amplitude can have a singularity
of order one. In a disk of radius ε its absolute integral is of order ε,
uniformly in the centre. The quadratic Schur estimate below uses only the
two marginal mass bounds and applies to nonsymmetric kernels as well. -/
namespace TransportOkaGrauert.SchurRemainder
noncomputable section
open MeasureTheory Set Metric Complex Filter

def profile (r t : ℝ) : ℝ := if t ∈ Ioo 0 r then t⁻¹ else 0

private theorem weighted (r t : ℝ) :
    t ^ (Module.finrank ℝ ℂ - 1) • profile r t = (Ioo (0:ℝ) r).indicator (fun _ => (1:ℝ)) t := by
  by_cases h : t ∈ Ioo (0:ℝ) r
  · simp [Complex.finrank_real_complex,profile,h,h.1.ne',smul_eq_mul]
  · simp [Complex.finrank_real_complex,profile,h]

theorem near_integrable (r : ℝ) : Integrable (fun z : ℂ => profile r ‖z‖) := by
  rw [integrable_fun_norm_addHaar (volume : Measure ℂ)]
  simp_rw [weighted]
  apply Integrable.integrableOn
  exact (integrable_indicator_iff measurableSet_Ioo).mpr
    (integrableOn_const (measure_Ioo_lt_top : volume (Ioo (0:ℝ) r) < ⊤).ne)

theorem near_mass {r : ℝ} (hr : 0 ≤ r) :
    (∫ z : ℂ, profile r ‖z‖) = 2 * Real.pi * r := by
  rw [integral_fun_norm_addHaar (volume : Measure ℂ) (profile r)]
  simp_rw [weighted]
  rw [setIntegral_indicator measurableSet_Ioo,inter_eq_right.mpr (fun _ h => h.1)]
  simp [Complex.finrank_real_complex,Measure.real,Complex.volume_ball,Real.volume_Ioo,
    ENNReal.toReal_ofReal hr,nsmul_eq_mul,smul_eq_mul]
  ring

theorem near_mass_at (x : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    (∫ y : ℂ, profile r ‖y-x‖) = 2 * Real.pi * r :=
  (integral_sub_right_eq_self (fun y : ℂ => profile r ‖y‖) x).trans (near_mass hr)

/-- If the two marginal masses of a nonnegative kernel are bounded by δ,
the bilinear form on pairs of unit-energy test functions is bounded by δ.
Integrability is stated on the product to allow a singular diagonal. -/
theorem schur_unit {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]
    (K : X → Y → ℝ) (f : X → ℝ) (g : Y → ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hK : ∀ x y, 0 ≤ K x y)
    (hr : ∀ x, (∫ y, K x y ∂ν) ≤ δ) (hc : ∀ y, (∫ x, K x y ∂μ) ≤ δ)
    (hf : Integrable (fun x => f x ^ 2) μ) (hg : Integrable (fun y => g y ^ 2) ν)
    (nf : (∫ x, f x ^ 2 ∂μ) ≤ 1) (ng : (∫ y, g y ^ 2 ∂ν) ≤ 1)
    (hF : Integrable (fun p : X × Y => K p.1 p.2 * f p.1 ^ 2) (μ.prod ν))
    (hG : Integrable (fun p : X × Y => K p.1 p.2 * g p.2 ^ 2) (μ.prod ν))
    (hFG : Integrable (fun p : X × Y => K p.1 p.2 * |f p.1 * g p.2|) (μ.prod ν)) :
    (∫ p : X × Y, K p.1 p.2 * |f p.1 * g p.2| ∂(μ.prod ν)) ≤ δ := by
  have row : (∫ p : X × Y, K p.1 p.2 * f p.1 ^ 2 ∂(μ.prod ν)) ≤ δ := by
    rw [integral_prod _ hF]
    calc
      _ ≤ ∫ x, δ * f x ^ 2 ∂μ := by
        apply integral_mono hF.integral_prod_left (hf.const_mul _)
        intro x
        change (∫ y, K x y * f x ^ 2 ∂ν) ≤ δ * f x ^ 2
        rw [integral_mul_const]
        exact mul_le_mul_of_nonneg_right (hr x) (sq_nonneg _)
      _ ≤ δ := by rw [integral_const_mul]; simpa using mul_le_mul_of_nonneg_left nf hδ
  have col : (∫ p : X × Y, K p.1 p.2 * g p.2 ^ 2 ∂(μ.prod ν)) ≤ δ := by
    rw [integral_prod_symm _ hG]
    calc
      _ ≤ ∫ y, δ * g y ^ 2 ∂ν := by
        apply integral_mono hG.integral_prod_right (hg.const_mul _)
        intro y
        change (∫ x, K x y * g y ^ 2 ∂μ) ≤ δ * g y ^ 2
        rw [integral_mul_const]
        exact mul_le_mul_of_nonneg_right (hc y) (sq_nonneg _)
      _ ≤ δ := by rw [integral_const_mul]; simpa using mul_le_mul_of_nonneg_left ng hδ
  have B := integral_mono (hFG.const_mul 2) (hF.add hG) (fun p => by
    change 2 * (K p.1 p.2 * |f p.1 * g p.2|) ≤ K p.1 p.2 * f p.1 ^ 2 + K p.1 p.2 * g p.2 ^ 2
    rw [abs_mul]
    have T : 2 * (|f p.1| * |g p.2|) ≤ f p.1 ^ 2 + g p.2 ^ 2 := by
      nlinarith [sq_nonneg (|f p.1| - |g p.2|),sq_abs (f p.1),sq_abs (g p.2)]
    nlinarith [mul_le_mul_of_nonneg_left T (hK p.1 p.2)])
  simp only [Pi.add_apply,integral_const_mul,integral_add hF hG] at B
  linarith

/-- Applied to the actual near-diagonal comparison kernel. The absolute
bilinear norm is bounded by the radius times 2π, uniformly at all centres. -/
theorem near_diagonal {r : ℝ} (hr : 0 ≤ r) (f g : ℂ → ℝ)
    (hf : Integrable (fun z => f z ^ 2)) (hg : Integrable (fun z => g z ^ 2))
    (nf : (∫ z, f z ^ 2) ≤ 1) (ng : (∫ z, g z ^ 2) ≤ 1)
    (hF : Integrable (fun p : ℂ × ℂ => profile r ‖p.1-p.2‖ * f p.1 ^ 2))
    (hG : Integrable (fun p : ℂ × ℂ => profile r ‖p.1-p.2‖ * g p.2 ^ 2))
    (hFG : Integrable (fun p : ℂ × ℂ => profile r ‖p.1-p.2‖ * |f p.1 * g p.2|)) :
    (∫ p : ℂ × ℂ, profile r ‖p.1-p.2‖ * |f p.1 * g p.2|) ≤ 2 * Real.pi * r := by
  apply schur_unit (μ := volume) (ν := volume) (fun x y => profile r ‖x-y‖) f g
    (by positivity) _ _ _ hf hg nf ng hF hG hFG
  · intro x y
    change 0 ≤ profile r ‖x-y‖
    by_cases h : ‖x-y‖ ∈ Ioo (0:ℝ) r <;> simp [profile,h]
  · intro x
    simpa only [norm_sub_rev x] using (near_mass_at x hr).le
  · exact fun y => (near_mass_at y hr).le

end
end TransportOkaGrauert.SchurRemainder
