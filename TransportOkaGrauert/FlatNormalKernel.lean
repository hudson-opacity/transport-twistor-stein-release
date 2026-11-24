import TransportOkaGrauert.FlatNormalSymbol
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.Prod

/-! # The Cartesian kernel for the damped ray average
The reference Fourier multiplier is convolution by exp(-|z|)/(2π|z|).
This fixes the coefficient and the choice of area measure when subtracting
its singularity from the curved geodesic normal kernel. -/
namespace TransportOkaGrauert.FlatNormalSymbol
noncomputable section
open Complex MeasureTheory Metric Set AddCircle
local instance : Fact (0 < 2*Real.pi) := ⟨Real.two_pi_pos⟩

def cartesianDensity (u : ℂ) : ℝ := Real.exp (-‖u‖) / ‖u‖

theorem cartesian_kernel {f : ℂ → ℂ} (hf : Continuous f) {C : ℝ} (bounded : ∀ x, ‖f x‖ ≤ C) (z : ℂ) :
    rayAverage f z = (2*Real.pi)⁻¹ • ∫ u : ℂ, cartesianDensity u • f (z+u) := by
  let H (w : AddCircle (2*Real.pi)) := ∫ t : ℝ in Ioi 0, (Real.exp (-t):ℂ)*f (z+t • (w.toCircle:ℂ))
  let Q (p : ℝ × ℝ) := (Real.exp (-p.1):ℂ)*f (z+p.1 • (Circle.exp p.2:ℂ))
  have cQ : Continuous Q := by unfold Q; fun_prop
  let radii := Ioi (0:ℝ)
  let angles := Ioo (-Real.pi) Real.pi
  have bQ (p : ℝ × ℝ) : ‖Q p‖ ≤ Real.exp (-p.1) * C := by
    simp only [Q,norm_mul,Complex.norm_real,Real.norm_of_nonneg (Real.exp_pos _).le]
    exact mul_le_mul_of_nonneg_left (bounded _) (Real.exp_pos _).le
  have integr : Integrable Q ((volume.restrict radii).prod (volume.restrict angles)) := by
    apply ((integrableOn_exp_neg_Ioi 0).mul_prod (integrableOn_const (C := C)
      (measure_Ioo_lt_top : volume (Ioo (-Real.pi) Real.pi) < ⊤).ne)).mono'
      cQ.aestronglyMeasurable
    exact .of_forall bQ
  have form (s : ℝ) : H (s : AddCircle (2*Real.pi)) = ∫ t in radii, Q (t,s) := by
    have eq : AddCircle.toCircle (s : AddCircle (2*Real.pi)) = Circle.exp s := by
      rw [AddCircle.toCircle_apply_mk]; simp [Real.pi_ne_zero]
    simp [H,Q,radii,eq]
  have angular : rayAverage f z = (2*Real.pi)⁻¹ • ∫ a in angles, ∫ t in radii, Q (t,a) := by
    have avg := fourierCoeff_eq_intervalIntegral H 0 (-Real.pi)
    simp only [fourierCoeff,neg_zero,fourier_zero,one_smul,
      show -Real.pi + 2*Real.pi = Real.pi by ring,one_div,
      intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi),
      integral_Ioc_eq_integral_Ioo,form] at avg
    exact avg
  have swap : (∫ a in angles, ∫ t in radii, Q (t,a)) = ∫ p in radii ×ˢ angles, Q p := by
    change _ = ∫ p in radii ×ˢ angles, Q p ∂((volume : Measure ℝ).prod volume)
    rw [← Measure.prod_restrict]
    exact (integral_prod_symm _ integr).symm
  rw [angular,swap,← Complex.integral_comp_polarCoord_symm (fun u => cartesianDensity u • f (z+u))]
  congr 1
  apply setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
  intro p hp
  have ht : 0 < p.1 := hp.1
  have polar : Complex.polarCoord.symm p = p.1 • (Circle.exp p.2 : ℂ) := by
    simp [Complex.real_smul,Circle.coe_exp,Complex.exp_mul_I,mul_add]
  change (Real.exp (-p.1):ℂ)*f (z+p.1 • (Circle.exp p.2:ℂ)) =
    p.1 • (cartesianDensity (Complex.polarCoord.symm p) • f (z+Complex.polarCoord.symm p))
  rw [smul_smul,cartesianDensity,Complex.norm_polarCoord_symm,abs_of_pos ht,
    show p.1 * (Real.exp (-p.1)/p.1) = Real.exp (-p.1) by field_simp [ht.ne'],polar]
  rfl

end
end TransportOkaGrauert.FlatNormalSymbol
