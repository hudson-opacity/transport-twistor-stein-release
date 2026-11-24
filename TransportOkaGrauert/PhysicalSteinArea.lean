import TransportOkaGrauert.PhysicalStein

/-! # Base area on transport-complex lines

The projected Jacobian of a transport-complex tangent line is nonnegative
and vanishes precisely on vertical tangent lines. In the vertical line the
physical complex structure is ordinary multiplication by the imaginary unit.
-/

noncomputable section
namespace TransportOkaGrauert.PhysicalStein

open Complex ChartStein
open scoped ComplexConjugate

/-- Evaluation of the standard oriented area form of the base plane. -/
def planeArea (u v : ℂ) : ℝ := u.re * v.im - u.im * v.re

private theorem area_coframe (m u v : ℂ) :
    planeArea (u-m*conj u) (v-m*conj v) = (1-normSq m)*planeArea u v := by
  simp [planeArea,Complex.normSq_apply,Complex.mul_re,Complex.mul_im]
  ring

theorem base_area_identity (σ : ℂ → ℝ) {p : E} (hp : ‖p.2‖ < 1) (v : E) :
    (1-normSq (p.2^2)) * planeArea v.1 (J σ p v).1 = normSq (v.1 - p.2^2*conj v.1) := by
  have eq := congrArg Prod.fst (coframe_J σ hp v)
  change (J σ p v).1 - p.2^2*conj (J σ p v).1 = I*(v.1-p.2^2*conj v.1) at eq
  rw [← area_coframe,eq]
  simp [planeArea,Complex.normSq_apply,Complex.mul_im,Complex.mul_re]
  ring

theorem base_area_pos_iff (σ : ℂ → ℝ) {p : E} (hp : ‖p.2‖ < 1) (v : E) :
    0 < planeArea v.1 (J σ p v).1 ↔ v.1 ≠ 0 := by
  have mulpos : 0 < 1-normSq (p.2^2) := by
    rw [Complex.normSq_eq_norm_sq,norm_pow]
    nlinarith [pow_lt_one₀ (norm_nonneg p.2) hp (by decide : 4 ≠ 0)]
  rw [← mul_pos_iff_of_pos_left mulpos,base_area_identity σ hp,Complex.normSq_pos]
  exact not_congr (SteinDivisor.firstIntegral_interior_zero_iff _ _ hp)

theorem base_area_nonneg (σ : ℂ → ℝ) {p : E} (hp : ‖p.2‖ < 1) (v : E) :
    0 ≤ planeArea v.1 (J σ p v).1 := by
  by_cases h : v.1 = 0
  · simp [planeArea,h]
  · exact ((base_area_pos_iff σ hp v).mpr h).le

theorem vertical_J (σ : ℂ → ℝ) {p : E} (hp : ‖p.2‖ < 1) (w : ℂ) :
    J σ p (0,w) = (0,I*w) := by
  apply (coframe_bijective σ hp).1
  rw [coframe_J σ hp]
  simp [coframe_apply,smul_eq_mul]

end TransportOkaGrauert.PhysicalStein
