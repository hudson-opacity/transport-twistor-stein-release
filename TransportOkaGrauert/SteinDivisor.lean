import TransportOkaGrauert.FlatScalar
import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# The fibre divisor on an oriented Riemannian surface

In an oriented orthonormal frame, `w` represents the distance gradient and `v`
represents a tangent vector. We use the existing polynomial
`FlatScalar.firstIntegral w μ = w − μ² conj w`. The results below check its
zero locus and the transport equation from the rank-one formula for the Hessian
of squared distance. Curves and their derivatives have an ordinary real parameter.
-/

namespace TransportOkaGrauert.SteinDivisor

open FlatScalar
open scoped ComplexConjugate Topology
noncomputable section

/-- Components of the vector `w` along `v` and its positive quarter-turn. -/
def longitudinal (w v : ℂ) : ℝ := (w * conj v).re

def transverse (w v : ℂ) : ℝ := (w * conj v).im

/-- For a surface distance gradient, the covariant derivative in direction `v`
has the form `v + c ⟨Jw,v⟩ Jw`. -/
def rankOneHessian (c : ℝ) (w v : ℂ) : ℂ :=
  v + (c * longitudinal (Complex.I * w) v : ℝ) * (Complex.I * w)

/-- Contracting the Hessian with `Jv` gives the transport derivative of
`⟨w,Jv⟩` along a geodesic. -/
theorem transverse_rankOneHessian (c : ℝ) (w v : ℂ) :
    transverse (rankOneHessian c w v) v = -c * longitudinal w v * transverse w v := by
  simp [rankOneHessian, transverse, longitudinal, Complex.mul_re, Complex.mul_im]
  ring

/-- On the unit sphere the polynomial is the signed transverse component times
`2iv`. This identity also holds at zeros of the distance gradient. -/
theorem firstIntegral_on_unit (w v : ℂ) (hv : v * conj v = 1) :
    firstIntegral w v = 2 * Complex.I * v * (transverse w v : ℂ) := by
  calc
    firstIntegral w v = v * (w * conj v - conj (w * conj v)) := by
      simp only [firstIntegral, map_mul, starRingEnd_self_apply]
      linear_combination -w * hv
    _ = _ := by rw [Complex.sub_conj]; simp [transverse]; ring

/-- On the unit sphere the zero directions are exactly those parallel to `w`. -/
theorem firstIntegral_unit_zero_iff (w v : ℂ) (hv : v * conj v = 1) :
    firstIntegral w v = 0 ↔ transverse w v = 0 := by
  have hv' : v ≠ 0 := by rintro rfl; simp at hv
  simp [firstIntegral_on_unit w v hv, hv', Complex.I_ne_zero]

/-- A unit direction is a zero of the fibre polynomial precisely when the
vector coefficient is a real multiple of that direction. -/
theorem firstIntegral_unit_zero_iff_parallel (w v : ℂ) (hv : v * conj v = 1) :
    firstIntegral w v = 0 ↔ ∃ a : ℝ, w = a * v := by
  rw [firstIntegral_unit_zero_iff w v hv]
  constructor
  · intro h
    have h' : w * conj v = (longitudinal w v : ℂ) := by
      apply Complex.ext
      · rfl
      · exact h
    refine ⟨longitudinal w v, ?_⟩
    rw [← h']
    linear_combination -w * hv
  · rintro ⟨a, rfl⟩
    simp [transverse, mul_assoc, hv]

/-- The disk extension is holomorphic for each fixed vector coefficient. -/
theorem firstIntegral_fibre_holomorphic (w : ℂ) : Differentiable ℂ (firstIntegral w) := by
  unfold firstIntegral
  fun_prop

/-- A quantitative interior bound on the fibre polynomial. -/
theorem firstIntegral_norm_lower_bound (w μ : ℂ) :
    (1 - ‖μ‖ ^ 2) * ‖w‖ ≤ ‖firstIntegral w μ‖ := by
  calc
    _ = ‖w‖ - ‖μ ^ 2 * conj w‖ := by rw [norm_mul, norm_pow, Complex.norm_conj]; ring
    _ ≤ _ := norm_sub_norm_le w (μ ^ 2 * conj w)

/-- At all interior fibre points the polynomial vanishes precisely at a zero of
its vector coefficient. -/
theorem firstIntegral_interior_zero_iff (w μ : ℂ) (hμ : ‖μ‖ < 1) :
    firstIntegral w μ = 0 ↔ w = 0 := by
  constructor
  · intro h
    by_contra hn
    have hμ' : 0 < 1 - ‖μ‖ ^ 2 := by nlinarith [norm_nonneg μ]
    have hpos := mul_pos hμ' (norm_pos_iff.mpr hn)
    simpa [h] using hpos.trans_le (firstIntegral_norm_lower_bound w μ)
  · rintro rfl
    simp [firstIntegral]

/-- The columns of the real-linear map `w ↦ w − μ² conj w` have this
determinant in the oriented basis `(1,i)`. -/
theorem firstIntegral_real_determinant (μ : ℂ) :
    (firstIntegral 1 μ).re * (firstIntegral Complex.I μ).im -
        (firstIntegral Complex.I μ).re * (firstIntegral 1 μ).im = 1 - ‖μ‖ ^ 4 := by
  rw [show ‖μ‖ ^ 4 = Complex.normSq μ ^ 2 by rw [Complex.normSq_eq_norm_sq]; ring]
  simp [firstIntegral, pow_two, Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
  ring

/-- Multiplication by an invertible integrating factor preserves the divisor. -/
theorem corrected_interior_zero_iff (u w μ : ℂ) (hu : u ≠ 0) (hμ : ‖μ‖ < 1) :
    u * firstIntegral w μ = 0 ↔ w = 0 := by
  simp [hu, firstIntegral_interior_zero_iff w μ hμ]

/-- In a frame rotating with connection speed `ω`, the two connection terms
cancel in the derivative of the transverse component. -/
theorem transverse_hasDerivAt {w v : ℝ → ℂ} {t c ω : ℝ}
    (hw : HasDerivAt w (rankOneHessian c (w t) (v t) - Complex.I * ω * w t) t)
    (hv : HasDerivAt v (-Complex.I * ω * v t) t) :
    HasDerivAt (fun s => transverse (w s) (v s))
      (-c * longitudinal (w t) (v t) * transverse (w t) (v t)) t := by
  have hvc : HasDerivAt (fun s => conj (v s)) (conj (-Complex.I * ω * v t)) t := hv.star
  have hp := hw.mul hvc
  have hcancel : (rankOneHessian c (w t) (v t) - Complex.I * ω * w t) * conj (v t) +
      w t * conj (-Complex.I * ω * v t) = rankOneHessian c (w t) (v t) * conj (v t) := by
    simp; ring
  rw [hcancel] at hp
  rw [← transverse_rankOneHessian]
  exact Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hp

/-- The fibre polynomial solves the scalar transport equation along a framed
unit geodesic. The hypotheses specify the two component derivatives at `t`. -/
theorem firstIntegral_hasDerivAt {w v : ℝ → ℂ} {t c ω : ℝ}
    (unit : ∀ᶠ s in 𝓝 t, v s * conj (v s) = 1)
    (hw : HasDerivAt w (rankOneHessian c (w t) (v t) - Complex.I * ω * w t) t)
    (hv : HasDerivAt v (-Complex.I * ω * v t) t) :
    HasDerivAt (fun s => firstIntegral (w s) (v s))
      ((-Complex.I * ω - (c * longitudinal (w t) (v t) : ℝ)) * firstIntegral (w t) (v t)) t := by
  rw [firstIntegral_on_unit _ _ unit.self_of_nhds]
  have h := (hv.const_mul (2 * Complex.I)).mul (transverse_hasDerivAt hw hv).ofReal_comp
  apply HasDerivAt.congr_of_eventuallyEq _ (unit.mono (fun s hs => firstIntegral_on_unit (w s) (v s) hs))
  convert h using 1
  push_cast
  ring

/-- The corrected divisor is constant to first order after multiplying by a
solution of the scalar integrating-factor equation. -/
theorem corrected_hasDerivAt_zero {w v u : ℝ → ℂ} {t c ω : ℝ}
    (unit : ∀ᶠ s in 𝓝 t, v s * conj (v s) = 1)
    (hw : HasDerivAt w (rankOneHessian c (w t) (v t) - Complex.I * ω * w t) t)
    (hv : HasDerivAt v (-Complex.I * ω * v t) t)
    (hu : HasDerivAt u ((Complex.I * ω + (c * longitudinal (w t) (v t) : ℝ)) * u t) t) :
    HasDerivAt (fun s => u s * firstIntegral (w s) (v s)) 0 t := by
  convert hu.mul (firstIntegral_hasDerivAt unit hw hv) using 1
  ring

end
end TransportOkaGrauert.SteinDivisor
