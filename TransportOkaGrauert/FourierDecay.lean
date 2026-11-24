import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Tactic

/-! Absolute summability of the angular Fourier coefficients of a twice
continuously differentiable periodic function, by integration by parts. -/

namespace TransportOkaGrauert.FourierDecay

noncomputable section
open Real Complex AddCircle Filter MeasureTheory
open scoped Real ContDiff

local notation "T" => (2 * π)
local instance : Fact (0 < T) := ⟨Real.two_pi_pos⟩

private abbrev coeff (g : ℝ → ℂ) := fourierCoeffOn Real.two_pi_pos g

/-- Integration by parts gains one angular frequency with no boundary term. -/
theorem derivative_coefficient (g : ℝ → ℂ) (hp : g.Periodic T)
    (hd : Differentiable ℝ g) (hc : Continuous (deriv g)) (n : ℤ) (hn : n ≠ 0) :
    coeff (deriv g) n = (I * n) * coeff g n := by
  have hx : g T = g 0 := by simpa using hp 0
  have h := fourierCoeffOn_of_hasDerivAt Real.two_pi_pos hn
    (fun t _ => (hd t).hasDerivAt) (hc.intervalIntegrable 0 T)
  rw [hx, sub_self, mul_zero, zero_sub, ofReal_zero, sub_zero] at h
  change _ = _ * fourierCoeffOn Real.two_pi_pos g n
  rw [h]
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  simp only [ofReal_mul, ofReal_ofNat]
  field_simp

private theorem periodic_deriv (g : ℝ → ℂ) (hp : g.Periodic T) : (deriv g).Periodic T := by
  intro t
  rw [← deriv_comp_add_const, show (fun x => g (x + T)) = g from funext hp]

/-- The same L¹-average bounds each Fourier coefficient. -/
private theorem coeff_bound (g : ℝ → ℂ) (n : ℤ) :
    ‖coeff g n‖ ≤ (1 / T) * ∫ t : ℝ in 0..T, ‖g t‖ := by
  rw [coeff, fourierCoeffOn_eq_integral]
  simp only [sub_zero, norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr Real.two_pi_pos)]
  gcongr
  have hw (x : AddCircle (T - 0)) : ‖fourier (-n) x‖ = 1 := Circle.norm_coe _
  simpa only [norm_smul, hw, one_mul] using
    intervalIntegral.norm_integral_le_integral_norm (μ := volume) (f := fun t : ℝ =>
      fourier (-n) (t : AddCircle (T - 0)) • g t) Real.two_pi_pos.le

/-- Absolute summability of all, positive and negative, modes. The regularity
hypothesis is expressed on the ordinary periodic lift to `ℝ`. -/
theorem summable_fourierCoeff_norm (f : AddCircle T → ℂ)
    (hf : ContDiff ℝ 2 (fun t : ℝ => f t)) : Summable (fun n : ℤ => ‖fourierCoeff f n‖) := by
  let g : ℝ → ℂ := fun t => f t
  have hp : g.Periodic T := fun t => congrArg f (AddCircle.coe_add_period T t)
  have h₁ : ContDiff ℝ 1 (deriv g) := hf.deriv'
  have h₂ : ContDiff ℝ 0 (deriv (deriv g)) := h₁.deriv'
  have hcoeff (n : ℤ) : fourierCoeff f n = coeff g n := by
    rw [coeff, fourierCoeffOn_eq_integral, fourierCoeff_eq_intervalIntegral _ _ 0]
    simp [g]
  let C := (1 / T) * ∫ t : ℝ in 0..T, ‖deriv (deriv g) t‖
  apply ((Real.summable_one_div_int_pow.mpr (by decide : 1 < 2)).mul_left C).of_norm_bounded_eventually
  filter_upwards [Filter.eventually_cofinite_ne (0 : ℤ)] with n hn
  have h := derivative_coefficient g hp (hf.differentiable (by decide)) h₁.continuous n hn
  have h' := derivative_coefficient (deriv g) (periodic_deriv g hp)
    (h₁.differentiable (by decide)) h₂.continuous n hn
  have hb := coeff_bound (deriv (deriv g)) n
  rw [h', h, norm_mul, norm_mul, norm_mul, norm_I, one_mul] at hb
  rw [Real.norm_eq_abs, abs_norm, hcoeff]
  have hnr : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  rw [mul_one_div, le_div_iff₀ (sq_pos_of_ne_zero hnr)]
  simp only [norm_mul, norm_I, one_mul, Complex.norm_intCast, ← mul_assoc, ← sq, sq_abs] at hb
  simpa only [mul_comm, C] using hb

end
end TransportOkaGrauert.FourierDecay
