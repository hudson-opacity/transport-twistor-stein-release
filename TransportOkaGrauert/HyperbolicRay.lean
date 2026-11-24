import TransportOkaGrauert.HyperbolicCR
import TransportOkaGrauert.HyperbolicRayAlgebra
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! # Explicit arclength geodesics for the conformal Poincaré disk

The disk automorphism sends the radial hyperbolic line through zero to
the required initial point. Its denominator stays in the right half-plane,
so its argument gives a single smooth real lift of the velocity direction.
-/

noncomputable section
namespace TransportOkaGrauert.HyperbolicRay

open Complex HyperbolicDisk HyperbolicCR
open scoped ComplexConjugate

def path (c : ℝ) (z₀ : ℂ) (θ₀ t : ℝ) : ℂ :=
  mob ((c : ℂ)*z₀) ((Circle.exp θ₀ : ℂ) * (Real.tanh (c*t) : ℂ)) / (c : ℂ)

def angle (c : ℝ) (z₀ : ℂ) (θ₀ t : ℝ) : ℝ :=
  θ₀ - 2 * arg (1 + conj ((c : ℂ)*z₀) * ((Circle.exp θ₀ : ℂ) * (Real.tanh (c*t) : ℂ)))

theorem angle_zero (c : ℝ) (z₀ : ℂ) (θ₀ : ℝ) : angle c z₀ θ₀ 0 = θ₀ := by simp [angle]

private theorem tanh_derivative (x : ℝ) : HasDerivAt Real.tanh (1 - Real.tanh x ^ 2) x := by
  rw [Real.tanh_eq_sinh_div_cosh]
  convert (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) (Real.cosh_pos x).ne' using 1
  · funext; rw [Real.tanh_eq_sinh_div_cosh]; rfl
  · field_simp [(Real.cosh_pos x).ne']

private theorem exp_angle_formula (θ : ℝ) {D : ℂ} (hd : D ≠ 0) :
    (Circle.exp (θ - 2 * arg D) : ℂ) = (Circle.exp θ : ℂ) * conj D / D := by
  let a := (Circle.exp (arg D) : ℂ)
  have ha : a ≠ 0 := (Circle.exp (arg D)).coe_ne_zero
  have he : (‖D‖ : ℂ) * a = D := norm_mul_exp_arg_mul_I D
  have hc : (‖D‖ : ℂ) * a⁻¹ = conj D := by
    simpa only [map_mul, conj_ofReal, a, ← Circle.coe_inv_eq_conj, Circle.coe_inv] using congrArg conj he
  rw [two_mul, Circle.exp_sub, Circle.exp_add, Circle.coe_div, Circle.coe_mul]
  change (Circle.exp θ : ℂ) / (a*a) = _
  calc
    _ = (Circle.exp θ : ℂ) * ((‖D‖ : ℂ) * a⁻¹) / ((‖D‖ : ℂ) * a) := by
      field_simp [ha, Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hd)]
    _ = _ := by rw [hc, he]

private theorem mob_hasDeriv {s v : ℂ} {r r' t : ℝ} (u : ℝ → ℝ)
    (h : HasDerivAt u r' t) (hr : u t = r) (hd : 1 + conj s * (v * (r : ℂ)) ≠ 0) :
    HasDerivAt (fun x => mob s (v * (u x : ℂ)))
      (v * (1 - s * conj s) * r' / (1 + conj s * (v * (r : ℂ))) ^ 2) t := by
  have du : HasDerivAt (fun x => (u x : ℂ)) (r' : ℂ) t := ofRealCLM.hasFDerivAt.comp_hasDerivAt t h
  have dw := du.const_mul v
  have dn := dw.const_add s
  have dd := (dw.const_mul (conj s)).const_add 1
  have hd' : 1 + conj s * (v * (u t : ℂ)) ≠ 0 := hr ▸ hd
  have d := dn.mul (((hasDerivAt_inv (𝕜 := ℂ) hd').hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t dd)
  convert d using 1
  change _ = v * (r' : ℂ) * (1 + conj s * (v * (u t : ℂ)))⁻¹ +
    (s + v * (u t : ℂ)) * ((conj s * (v * r')) * (-((1 + conj s * (v * (u t : ℂ)))^2)⁻¹))
  rw [hr]
  field_simp [hd]
  ring

private theorem arg_den_hasDeriv {s v : ℂ} {r r' t : ℝ} (u : ℝ → ℝ)
    (h : HasDerivAt u r' t) (hr : u t = r) (hd : 1 + conj s * (v * (r : ℂ)) ∈ slitPlane) :
    HasDerivAt (fun x => arg (1 + conj s * (v * (u x : ℂ))))
      (r' * ((conj s * v) / (1 + conj s * (v * (r : ℂ)))).im) t := by
  have du : HasDerivAt (fun x => (u x : ℂ)) (r' : ℂ) t := ofRealCLM.hasFDerivAt.comp_hasDerivAt t h
  have dd := ((du.const_mul v).const_mul (conj s)).const_add 1
  have dd' : 1 + conj s * (v * (u t : ℂ)) ∈ slitPlane := hr ▸ hd
  have dl := ((Complex.hasDerivAt_log dd').hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t dd
  have di := imCLM.hasFDerivAt.comp_hasDerivAt t dl
  convert di using 1
  · funext; exact (log_im _).symm
  · change _ = ((conj s * (v * r')) * (1 + conj s * (v * (u t : ℂ)))⁻¹).im
    rw [hr, show (conj s * (v * r')) * (1 + conj s * (v * (r : ℂ)))⁻¹ =
      (r' : ℂ) * ((conj s * v) / (1 + conj s * (v * (r : ℂ)))) by ring]
    simp

private theorem drift_formula {c : ℝ} {z : ℂ} (hs : 0 < 1 - c^2 * normSq z) (w : Circle) :
    Real.exp (-factor c z) * Isothermal.angularDrift (factor c) z w =
      -(2*c^2) * ((conj z) * (w : ℂ)).im := by
  rw [factor, neg_neg, Real.exp_log hs, Isothermal.angularDrift,
    factor_fderiv_apply hs.ne', factor_fderiv_apply hs.ne']
  simp only [I_re, I_im, one_re, one_im, mul_zero, mul_one, zero_add, add_zero,
    mul_im, conj_re, conj_im]
  field_simp [hs.ne']
  ring

/-- The explicit path and real velocity lift solve both unit-speed geodesic
equations, at every real time. -/
theorem equations {c : ℝ} {z₀ : ℂ} (hc : 0 < c) (hc' : c < 1) (hz : ‖z₀‖ ≤ 1) (θ₀ t : ℝ) :
    HasDerivAt (path c z₀ θ₀)
      ((Real.exp (-factor c (path c z₀ θ₀ t)) : ℂ) * (Circle.exp (angle c z₀ θ₀ t) : ℂ)) t ∧
    HasDerivAt (angle c z₀ θ₀)
      (Real.exp (-factor c (path c z₀ θ₀ t)) *
        Isothermal.angularDrift (factor c) (path c z₀ θ₀ t) (Circle.exp (angle c z₀ θ₀ t))) t := by
  let s := (c : ℂ)*z₀
  let v := (Circle.exp θ₀ : ℂ)
  let u (x : ℝ) := Real.tanh (c*x)
  let D := 1 + conj s*(v*(u t:ℂ))
  let m := mob s (v*(u t:ℂ))
  have hcC : (c:ℂ) ≠ 0 := ofReal_ne_zero.mpr hc.ne'
  have hv : ‖v‖ = 1 := Circle.norm_coe _
  have hs : ‖s‖ < 1 := by
    rw [show ‖s‖ = c*‖z₀‖ by simp [s, abs_of_pos hc]]
    exact (mul_le_of_le_one_right hc.le hz).trans_lt hc'
  have huw : ‖v*(u t:ℂ)‖ < 1 := by
    simpa only [norm_mul,hv,one_mul,Complex.norm_real,Real.norm_eq_abs,u] using Real.abs_tanh_lt_one (c*t)
  have hd : D ≠ 0 := nonzero hs huw.le
  have dsl : D ∈ slitPlane := by
    apply mem_slitPlane_iff.mpr
    left
    have hnorm : ‖conj s * (v * (u t : ℂ))‖ < 1 := by
      rw [norm_mul, norm_conj]
      exact (mul_le_of_le_one_right (norm_nonneg _) huw.le).trans_lt hs
    have hre := (abs_le.mp (abs_re_le_norm (conj s * (v * (u t : ℂ))))).1
    change 0 < 1 + (conj s * (v * (u t : ℂ)) ).re
    linarith
  have hm : ‖m‖ < 1 := norm_lt hs huw
  have hscale : 1 - c^2 * normSq (path c z₀ θ₀ t) = 1 - normSq m := by
    change 1 - c^2 * normSq (m/(c:ℂ)) = _
    simp only [map_div₀, normSq_ofReal, pow_two]
    field_simp [hc.ne']
  have hscl : 0 < 1 - c^2 * normSq (path c z₀ θ₀ t) := by
    rw [hscale, normSq_eq_norm_sq]
    nlinarith [mul_self_lt_mul_self (norm_nonneg m) hm]
  have he : Real.exp (-factor c (path c z₀ θ₀ t)) = 1 - normSq m := by
    rw [factor, neg_neg, Real.exp_log hscl, hscale]
  have hangle : (Circle.exp (angle c z₀ θ₀ t) : ℂ) = v*conj D/D := exp_angle_formula θ₀ hd
  have du : HasDerivAt u (c*(1-(u t)^2)) t := by
    have d := (tanh_derivative (c*t)).comp t ((hasDerivAt_id t).const_mul c)
    convert d using 1
    change c * (1 - (u t)^2) = (1 - (u t)^2) * (c * 1)
    ring
  constructor
  · have d := (mob_hasDeriv (s := s) (v := v) u du rfl hd).div_const (c : ℂ)
    convert d using 1
    rw [he,hangle]
    rw [show ((1-normSq m : ℝ):ℂ)*(v*conj D/D) = _ from HyperbolicRayAlgebra.speed hv hd]
    push_cast
    field_simp [hcC]
  · have d := (hasDerivAt_const t θ₀).sub ((arg_den_hasDeriv (s := s) (v := v) u du rfl dsl).const_mul 2)
    convert d using 1
    rw [drift_formula hscl, hangle]
    change -(2*c^2) * (conj (m / (c:ℂ)) * (v * conj D / D)).im = _
    have hh : conj (m / (c:ℂ)) * (v * conj D / D) =
        ((c⁻¹ : ℝ) : ℂ) * (conj m * (v * conj D / D)) := by
      rw [map_div₀,conj_ofReal,ofReal_inv]
      simp only [div_eq_mul_inv]
      ring
    have scale_im (b : ℝ) (w : ℂ) : ((b : ℂ) * w).im = b * w.im := by simp
    rw [hh, scale_im]
    have turn : (conj m * (v * conj D / D)).im = (1 - (u t)^2) * ((conj s*v)/D).im :=
      HyperbolicRayAlgebra.turn hv hd
    rw [turn]
    change -(2*c^2) * (c⁻¹ * ((1-(u t)^2) * ((conj s*v)/D).im)) =
      0 - 2 * (c*(1-(u t)^2)*((conj s*v)/D).im)
    field_simp [hc.ne']
    ring

end TransportOkaGrauert.HyperbolicRay
