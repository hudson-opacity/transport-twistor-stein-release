import TransportOkaGrauert.FlatNormalSymbol
import Mathlib.Analysis.Fourier.AddCircleMulti

/-! # The reference geodesic ray multiplier on a periodic chart
The plane is projected onto a square torus of side eight, leaving the closed
unit disk inside one fundamental square. Fourier inversion for continuous
periodic data uses the actual compact-group characters. -/
namespace TransportOkaGrauert.FlatNormalTorus
noncomputable section
open Complex MeasureTheory AddCircle UnitAddTorus FlatNormalSymbol
open scoped ComplexConjugate

abbrev Torus := UnitAddTorus (Fin 2)
abbrev Freq := Fin 2 → ℤ

def point (z : ℂ) : Torus := ![((z.re/8 : ℝ) : UnitAddCircle),((z.im/8 : ℝ) : UnitAddCircle)]
def frequency (k : Freq) : ℂ := ⟨Real.pi/4 * (k 0 : ℝ), Real.pi/4 * (k 1 : ℝ)⟩
def weight (k : Freq) := Real.sqrt (1+‖frequency k‖^2)

theorem character (k : Freq) (z : ℂ) : mFourier k (point z) = wave (frequency k) z := by
  change (∏ j : Fin 2, fourier (k j) (point z j)) = _
  rw [Fin.prod_univ_two]
  change fourier (k 0) ((z.re/8 : ℝ) : UnitAddCircle) * fourier (k 1) ((z.im/8 : ℝ) : UnitAddCircle) = _
  rw [fourier_coe_apply,fourier_coe_apply,← Complex.exp_add]
  unfold wave
  congr 1
  simp [frequency,directionPair,Complex.mul_re]
  ring

private theorem weight_pos (k : Freq) : 0 < weight k := Real.sqrt_pos.mpr (by positivity)

/-- On periodic data with one summable weighted derivative, the exact
inverse is a continuous periodic function and the ray-average identity
holds at every point of the plane. -/
theorem invert (f : C(Torus,ℂ)) (h : Summable (fun k : Freq => weight k * ‖mFourierCoeff f k‖)) :
    ∃ g : C(Torus,ℂ), ∀ z : ℂ, rayAverage (fun y => g (point y)) z = f (point z) := by
  let a (k : Freq) := mFourierCoeff f k
  let b (k : Freq) := (weight k : ℂ) * a k
  have hb : Summable (fun k => ‖b k‖) := by
    simpa only [b,a,norm_mul,Complex.norm_real,Real.norm_of_nonneg (weight_pos _).le] using h
  have ha : Summable (fun k => ‖a k‖) := h.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => by
    have w : 1 ≤ weight k := by
      exact (Real.le_sqrt (by norm_num) (by positivity)).mpr (by nlinarith [sq_nonneg ‖frequency k‖])
    exact le_mul_of_one_le_left (norm_nonneg _) w)
  have terms : Summable (fun k : Freq => b k • mFourier k) := .of_norm (by simpa [norm_smul,mFourier_norm] using hb)
  let g : C(Torus,ℂ) := ∑' k, b k • mFourier k
  refine ⟨g,fun z => ?_⟩
  have ge (x : ℂ) : g (point x) = ∑' k, b k * wave (frequency k) x := by
    let ev : C(Torus,ℂ) →L[ℂ] ℂ := ContinuousMap.evalCLM ℂ (point x)
    change ev (∑' k, b k • mFourier k) = _
    rw [ev.map_tsum terms]
    apply tsum_congr; intro k
    change b k * mFourier k (point x) = _
    rw [character]
  simp_rw [ge]
  rw [series_action b frequency hb]
  have fe := (hasSum_mFourier_series_apply_of_summable (f := f) ha.of_norm (point z)).tsum_eq
  rw [← fe]
  apply tsum_congr; intro k
  change (weight k : ℂ) * a k * wave (frequency k) z * (weight k : ℂ)⁻¹ = a k * mFourier k (point z)
  rw [character]
  field_simp [Complex.ofReal_ne_zero.mpr (weight_pos k).ne']

end
end TransportOkaGrauert.FlatNormalTorus
