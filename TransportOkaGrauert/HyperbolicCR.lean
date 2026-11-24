import TransportOkaGrauert.ChartStein
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Two transport-holomorphic endpoint maps on a Poincaré disk

The metric is `exp(2σ)|dz|²` with `σ = −log(1−c²|z|²)`. Differentiation
below is in the real coordinates of the fixed transport disk chart.
-/

noncomputable section
namespace TransportOkaGrauert.HyperbolicCR

open Complex ChartStein
open scoped ComplexConjugate ContDiff

def factor (c : ℝ) (z : ℂ) : ℝ := -Real.log (1 - c^2 * Complex.normSq z)

def endpoint (c ε : ℝ) (p : E) : ℂ :=
  ((c : ℂ)*p.1 + (ε : ℂ)*p.2) / (1 + conj ((c : ℂ)*p.1) * (ε : ℂ) * p.2)

theorem denom_ne {c ε : ℝ} {p : E} (hc : 0 < c) (hc' : c < 1)
    (hε : ε = 1 ∨ ε = -1) (hz : ‖p.1‖ ≤ 1) (hw : ‖p.2‖ ≤ 1) :
    1 + conj ((c : ℂ)*p.1) * (ε : ℂ) * p.2 ≠ 0 := by
  have hsign : ‖(ε : ℂ)‖ = 1 := by rcases hε with rfl | rfl <;> simp
  have hsmall : ‖conj ((c : ℂ)*p.1) * (ε : ℂ) * p.2‖ < 1 := by
    rw [norm_mul, norm_mul, Complex.norm_conj, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hc, hsign, mul_one]
    calc
      _ ≤ (c * 1) * 1 := by gcongr
      _ < 1 := by simpa
  intro he
  have eq : conj ((c : ℂ)*p.1) * (ε : ℂ) * p.2 = -1 := by linear_combination he
  rw [eq, norm_neg, norm_one] at hsmall
  exact lt_irrefl _ hsmall

theorem scale_pos {c : ℝ} {z : ℂ} (hc : 0 < c) (hc' : c < 1) (hz : ‖z‖ ≤ 1) :
    0 < 1 - c^2 * Complex.normSq z := by
  rw [Complex.normSq_eq_norm_sq]
  have h : c * ‖z‖ < 1 := lt_of_le_of_lt (mul_le_of_le_one_right hc.le hz) hc'
  nlinarith [mul_self_lt_mul_self (mul_nonneg hc.le (norm_nonneg z)) h, mul_pow c ‖z‖ 2]

private theorem scale_deriv (c : ℝ) (z : ℂ) :
    HasFDerivAt (fun z => 1 - c^2 * Complex.normSq z)
      (0 - c^2 • ((2 * z.re) • reCLM + (2 * z.im) • imCLM)) z := by
  have h := (hasFDerivAt_const (𝕜 := ℝ) (1 : ℝ) z).sub
    (((reCLM.hasFDerivAt.pow 2).add (imCLM.hasFDerivAt.pow 2)).const_mul (c^2))
  simpa [Pi.sub_def, Pi.add_def, Complex.normSq_apply, pow_two, two_smul, two_mul] using h

theorem factor_fderiv_apply {c : ℝ} {z : ℂ} (hs : 1 - c^2 * Complex.normSq z ≠ 0)
    (v : ℂ) : fderiv ℝ (factor c) z v =
      2 * c^2 * (z.re * v.re + z.im * v.im) / (1 - c^2 * Complex.normSq z) := by
  have d := ((scale_deriv c z).log hs).neg
  change HasFDerivAt (factor c) _ z at d
  rw [d.fderiv]
  simp [div_eq_mul_inv]
  ring

private def num (c ε : ℝ) (p : E) : ℂ := c*p.1 + ε*p.2
private def den (c ε : ℝ) (p : E) : ℂ := 1 + conj ((c:ℂ)*p.1) * ε * p.2

/-- Real differential of the rational endpoint in every horizontal and vertical direction. -/
theorem endpoint_fderiv_apply (c ε : ℝ) (p v : E)
    (hd : 1 + conj ((c : ℂ)*p.1) * (ε : ℂ) * p.2 ≠ 0) :
    fderiv ℝ (endpoint c ε) p v =
    (((c : ℂ)*v.1 + ε*v.2) * (1 + conj ((c : ℂ)*p.1) * ε * p.2) -
      (c*p.1 + ε*p.2) * (conj ((c:ℂ)*v.1)*ε*p.2 + conj ((c:ℂ)*p.1)*ε*v.2)) /
      (1 + conj ((c : ℂ)*p.1)*ε*p.2)^2 := by
  have a := (hasFDerivAt_fst (𝕜 := ℝ) (p := p)).const_mul (c : ℂ)
  have b := (hasFDerivAt_snd (𝕜 := ℝ) (p := p)).const_mul (ε : ℂ)
  have dN := a.add b
  have dD := (hasFDerivAt_const (𝕜 := ℝ) (1 : ℂ) p).add
    (((Complex.conjCLE.hasFDerivAt.comp p a).mul_const (ε : ℂ)).mul (hasFDerivAt_snd (𝕜 := ℝ) (p := p)))
  change HasFDerivAt (num c ε) _ p at dN
  change HasFDerivAt (den c ε) _ p at dD
  have d := dN.mul ((hasDerivAt_inv (𝕜 := ℂ) hd).hasFDerivAt.restrictScalars ℝ |>.comp p dD)
  change HasFDerivAt (fun y => num c ε y * (den c ε y)⁻¹) _ p at d
  rw [show endpoint c ε = _ from funext (fun y => div_eq_mul_inv (num c ε y) (den c ε y)), d.fderiv]
  simp [num, den, smul_eq_mul, mul_assoc]
  field_simp [hd]
  ring

theorem connection (c : ℝ) (p : E) (hs : 1 - c^2 * Complex.normSq p.1 ≠ 0) :
    connectionCoefficient (factor c) p =
      2 * (c : ℂ)^2 / ((1 - c^2 * Complex.normSq p.1 : ℝ) : ℂ) *
        p.2 * (p.2^2 * conj p.1 - p.1) := by
  let s := 1 - c^2 * Complex.normSq p.1
  have sx : fderiv ℝ (factor c) p.1 1 = 2 * c^2 * p.1.re / s := by
    simp [s, factor_fderiv_apply hs]
  have sy : fderiv ℝ (factor c) p.1 I = 2 * c^2 * p.1.im / s := by
    simp [s, factor_fderiv_apply hs]
  have hz : (p.1.re : ℂ) + p.1.im * I = p.1 := re_add_im _
  have hzc : (p.1.re : ℂ) - p.1.im * I = conj p.1 := by
    apply Complex.ext <;> simp
  unfold connectionCoefficient
  rw [sx,sy]
  change _ = 2 * (c : ℂ)^2 / (s : ℂ) * p.2 * _
  push_cast
  linear_combination (2*(c:ℂ)^2/(s:ℂ)*p.2^3)*hzc - (2*(c:ℂ)^2/(s:ℂ)*p.2)*hz

theorem endpoint_smooth (c ε : ℝ) (p : E) (hd : 1 + conj ((c : ℂ)*p.1) * (ε : ℂ) * p.2 ≠ 0) :
    ContDiffAt ℝ ∞ (endpoint c ε) p := by
  have hc : ContDiff ℝ ∞ (fun q : E => conj ((c:ℂ)*q.1)) :=
    Complex.conjCLE.contDiff.comp (contDiff_const.mul contDiff_fst)
  have hn : ContDiff ℝ ∞ (num c ε) :=
    (contDiff_const.mul contDiff_fst).add (contDiff_const.mul contDiff_snd)
  have hb : ContDiff ℝ ∞ (den c ε) := contDiff_const.add ((hc.mul contDiff_const).mul contDiff_snd)
  rw [show endpoint c ε = _ from funext (fun y => div_eq_mul_inv (num c ε y) (den c ε y))]
  exact hn.contDiffAt.mul ((contDiffAt_inv ℝ hd).comp p hb.contDiffAt)

theorem endpoint_hol {c ε : ℝ} {p : E} (hc : 0 < c) (hc' : c < 1) (hε : ε = 1 ∨ ε = -1)
    (hz : ‖p.1‖ < 1) (hw : ‖p.2‖ < 1) : HolAt (factor c) (endpoint c ε) p := by
  have hd := denom_ne hc hc' hε hz.le hw.le
  have hs := (scale_pos hc hc' hz.le).ne'
  have he : (ε : ℂ)^2 = 1 := by rcases hε with rfl | rfl <;> norm_num
  refine ⟨endpoint_smooth c ε p hd, ?_⟩
  let D := 1 + conj ((c:ℂ)*p.1) * (ε:ℂ) * p.2
  let N := (c:ℂ)*p.1 + (ε:ℂ)*p.2
  let s := ((1 - c^2 * Complex.normSq p.1 : ℝ) : ℂ)
  have s_eq : s = 1 - (c:ℂ)^2 * (p.1 * conj p.1) := by
    simp only [s, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_mul, Complex.ofReal_pow, Complex.mul_conj]
  have d_eq : D = 1 + (c:ℂ)*conj p.1 * (ε:ℂ) * p.2 := by simp [D]
  let A := (c : ℂ) / D
  let B := -N * (c : ℂ) * ε * p.2 / D^2
  let C := (ε : ℂ) * s / D^2
  have hD (v : E) : fderiv ℝ (endpoint c ε) p v = A*v.1 + B*conj v.1 + C*v.2 := by
    rw [endpoint_fderiv_apply c ε p v hd]
    change ((c*v.1+ε*v.2)*D - N*(conj ((c:ℂ)*v.1)*ε*p.2 + conj ((c:ℂ)*p.1)*ε*v.2))/D^2 = _
    simp only [A,B,C, map_mul, Complex.conj_ofReal]
    field_simp [show D ≠ 0 from hd]
    rw [d_eq, s_eq]
    dsimp [N]
    ring
  unfold SatisfiesCR
  simp only [hD, map_zero, map_one, Complex.conj_I,
    mul_zero, add_zero, zero_add, mul_one]
  constructor
  · ring
  · rw [connection c p hs]
    change p.2^2 * (A + B - I * (A * I + B * (-I))) +
      (A + B + I * (A * I + B * (-I))) - (2 * (c:ℂ)^2 / s * p.2 * (p.2^2 * conj p.1 - p.1)) * C = 0
    have e₁ : A + B - I * (A * I + B * (-I)) = 2*A := by linear_combination -(A-B)*Complex.I_sq
    have e₂ : A + B + I * (A * I + B * (-I)) = 2*B := by linear_combination (A-B)*Complex.I_sq
    rw [e₁,e₂]
    simp only [A,B,C]
    have hs' : s ≠ 0 := Complex.ofReal_ne_zero.mpr hs
    field_simp [show D ≠ 0 from hd, hs']
    rw [d_eq]
    dsimp [N]
    linear_combination -2*(c:ℂ)*p.2^2*he

private theorem factor_second {c : ℝ} {z : ℂ} (hs : 1 - c^2*normSq z ≠ 0) (v : ℂ) :
    fderiv ℝ (fun y => fderiv ℝ (factor c) y v) z v =
      (2*c^2*(v.re^2+v.im^2)*(1-c^2*normSq z) +
        4*c^4*(z.re*v.re+z.im*v.im)^2)/(1-c^2*normSq z)^2 := by
  have dd := scale_deriv c z
  have lin := ((reCLM.hasFDerivAt (x := z)).mul_const v.re).add
    ((imCLM.hasFDerivAt (x := z)).mul_const v.im)
  have d := (lin.const_mul (2*c^2)).mul ((hasDerivAt_inv hs).comp_hasFDerivAt z dd)
  change HasFDerivAt (fun y : ℂ => 2*c^2*(y.re*v.re+y.im*v.im)*(1-c^2*normSq y)⁻¹) _ z at d
  have actual := d.congr_of_eventuallyEq (f₁ := fun y => fderiv ℝ (factor c) y v) (by
    filter_upwards [dd.continuousAt.eventually_ne hs] with y hy
    exact (factor_fderiv_apply hy v).trans (div_eq_mul_inv _ _))
  rw [actual.fderiv]
  simp
  field_simp [hs]
  ring

/-- The curvature in the very same chart used for the CR equations is
constant and strictly negative for `0 < c < 1`. -/
theorem curvature_factor {c : ℝ} {z : ℂ} (hc : 0 < c) (hc' : c < 1) (hz : ‖z‖ ≤ 1) :
    SimpleDiskTarget.curvature (factor c) z = -4*c^2 := by
  have hs := scale_pos hc hc' hz
  have e : Real.exp (-2 * factor c z) = (1-c^2*normSq z)^2 := by
    rw [factor, show -2 * -Real.log (1-c^2*normSq z) = (2 : ℕ)*Real.log (1-c^2*normSq z) by norm_num,
      Real.exp_nat_mul, Real.exp_log hs]
  rw [SimpleDiskTarget.curvature, SimpleDiskTarget.laplacian, e,
    factor_second hs.ne', factor_second hs.ne']
  simp only [Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im, one_pow, zero_pow (by norm_num : 2 ≠ 0),
    zero_add, mul_zero, mul_one, add_zero]
  field_simp [hs.ne']
  rw [Complex.normSq_apply]
  ring

end TransportOkaGrauert.HyperbolicCR
