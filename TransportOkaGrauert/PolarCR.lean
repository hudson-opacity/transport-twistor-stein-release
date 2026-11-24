import TransportOkaGrauert.ConformalFrame
import TransportOkaGrauert.ChartStein

/-! Agreement of the real moving-frame complex structure with the bidisk transport CR equations. -/

noncomputable section

namespace TransportOkaGrauert.PolarCR

open Complex ConformalFrame
open scoped ContDiff ComplexConjugate

def polar (p : Chart) : ChartStein.E := (p.1, Real.exp p.2.2 • unit p.2.1)

private theorem normal_eq (θ : ℝ) : normal θ = I * unit θ := by
  simp [unit, normal, Complex.real_smul]
  ring_nf
  simp [Complex.I_sq]

private theorem unit_ne (θ : ℝ) : unit θ ≠ 0 := by
  intro hz
  have hc := congrArg Complex.re hz
  have hs := congrArg Complex.im hz
  simp [unit, -Complex.ofReal_cos, -Complex.ofReal_sin] at hc hs
  nlinarith [Real.sin_sq_add_cos_sq θ]

theorem polar_derivative (p w : Chart) :
    fderiv ℝ polar p w = (w.1, (polar p).2 * ((w.2.2 : ℂ) + I * w.2.1)) := by
  have du (θ : ℝ) : HasDerivAt unit (normal θ) θ :=
    ((Real.hasDerivAt_cos θ).smul_const (1 : ℂ)).add ((Real.hasDerivAt_sin θ).smul_const I)
  let θL : Chart →L[ℝ] ℝ := (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (.snd ℝ ℂ (ℝ × ℝ))
  let sL : Chart →L[ℝ] ℝ := (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (.snd ℝ ℂ (ℝ × ℝ))
  have hθ : HasDerivAt unit (normal p.2.1) (θL p) := du _
  have hd := (hasFDerivAt_fst (𝕜 := ℝ) (p := p)).prodMk
    ((sL.hasFDerivAt.exp).smul (hθ.hasFDerivAt.comp p θL.hasFDerivAt))
  rw [show fderiv ℝ polar p = _ from hd.fderiv]
  simp [θL,sL,polar,normal_eq,Complex.real_smul]
  ring

private theorem coordinates (D : ChartStein.E →L[ℝ] ℂ) (z v : ℂ) :
    D (z,v) = (z.re:ℂ)*D (1,0)+(z.im:ℂ)*D (I,0)+(v.re:ℂ)*D (0,1)+(v.im:ℂ)*D (0,I) := by
  have he : (z,v) = z.re • ((1,0) : ChartStein.E) + z.im • (I,0) + v.re • (0,1) + v.im • (0,I) := by
    ext <;> simp [Complex.real_smul]
  rw [he]
  simp only [map_add, map_smul, Complex.real_smul]

private theorem vert (D : ChartStein.E →L[ℝ] ℂ) (μ : ℂ) (hm : μ ≠ 0) :
    D (0,I*μ) = I*D (0,μ) ↔ D (0,I) = I*D (0,1) := by
  have eq : D (0,I*μ) - I*D (0,μ) = conj μ * (D (0,I)-I*D (0,1)) := by
    rw [coordinates D 0 (I*μ), coordinates D 0 μ]
    conv_rhs => rw [show conj μ = (μ.re:ℂ) - I*μ.im by apply Complex.ext <;> simp]
    simp only [Complex.zero_re, Complex.zero_im, Complex.ofReal_zero, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add, zero_sub, Complex.ofReal_neg]
    ring_nf
    simp [Complex.I_sq]
  rw [← sub_eq_zero, eq, mul_eq_zero, or_iff_right (show conj μ ≠ 0 by simpa using hm),
    sub_eq_zero]

private theorem coefficients (r c n sx sy A B C : ℂ) (hn : c^2+n^2=1) (hd : 1+r^2 ≠ 0) :
    let u := c + n*I
    let μ := r*u
    let t := (1-r^2)/(1+r^2)
    (1+r^2)*u*
      ((c*A+n*B + μ*I*(-n*sx+c*sy)*C) + I*t*(-n*A+c*B-μ*I*(c*sx+n*sy)*C)) =
      μ^2*(A-I*B)+(A+I*B) - μ*(μ^2*(sx-I*sy)-(sx+I*sy))*C := by
  dsimp only
  field_simp [hd]
  have hI := Complex.I_sq
  grind only

/-- The two bidisk CR equations are exactly complex linearity for the transported
complex structure under the real logarithmic-polar change of variables. -/
theorem satisfiesCR_iff {σ : ℂ → ℝ} (p : Chart) (hs : p.2.2 < 0) (D : ChartStein.E →L[ℝ] ℂ) :
    ChartStein.SatisfiesCR σ (polar p) D ↔
      ∀ w, D (fderiv ℝ polar p (J σ p w)) = I * D (fderiv ℝ polar p w) := by
  let L := D.comp (fderiv ℝ polar p)
  let r : ℂ := Real.exp p.2.2
  let c : ℂ := Real.cos p.2.1
  let n : ℂ := Real.sin p.2.1
  let u := c + n*I
  let μ := r*u
  let sx : ℂ := fderiv ℝ σ p.1 1
  let sy : ℂ := fderiv ℝ σ p.1 I
  let A := D (1,0)
  let B := D (I,0)
  let C := D (0,1)
  have he : 0 < Real.exp p.2.2 := Real.exp_pos _
  have hr : r ≠ 0 := by dsimp [r]; exact_mod_cast he.ne'
  have hu : unit p.2.1 = u := by simp [unit,u,c,n,Complex.real_smul]
  have hμ : (polar p).2 = μ := by simp [polar,μ,r,hu,Complex.real_smul]
  have un : u ≠ 0 := hu ▸ unit_ne _
  have hn : c^2+n^2=1 := by dsimp [c,n]; exact_mod_cast Real.cos_sq_add_sin_sq p.2.1
  have den : 1+r^2 ≠ 0 := by dsimp [r]; exact_mod_cast (show 1 + Real.exp p.2.2 ^ 2 ≠ 0 by positivity)
  have rad : (t p : ℂ) = (1-r^2)/(1+r^2) := by
    have heq : (Real.exp p.2.2)^2 = Real.exp (2*p.2.2) := by rw [← Real.exp_nat_mul]; rfl
    dsimp [t,radialParameter,r]
    norm_cast
    rw [heq]
  have ht : t p ≠ 0 := by
    have ht' : Real.exp (2*p.2.2) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    exact div_ne_zero (sub_pos.mpr ht').ne' (by positivity)
  have lr : L (R p) = D (0,μ) := by simp [L,polar_derivative,R,hμ]
  have lv : L (V p) = D (0,I*μ) := by simp [L,polar_derivative,V,hμ,mul_comm]
  change _ ↔ ∀ w, L (J σ p w) = I * L w
  rw [intertwines_iff σ p ht L, lr, lv, vert D μ (mul_ne_zero hr un)]
  unfold ChartStein.SatisfiesCR
  apply and_congr_right
  intro hv
  have dv (z v : ℂ) : D (z,v) = (z.re:ℂ)*A+(z.im:ℂ)*B+v*C := by
    rw [coordinates D z v,hv]
    conv_rhs => rw [← Complex.re_add_im v]
    dsimp only [A,B,C]
    ring
  let U := c*A+n*B + μ*I*(-n*sx+c*sy)*C
  let W := -n*A+c*B - μ*I*(c*sx+n*sy)*C
  have lx : L (X σ p) = (scale σ p : ℂ)*U := by
    simp only [L, ContinuousLinearMap.comp_apply, polar_derivative, hμ]
    change D (scale σ p • unit p.2.1, μ * ((0 : ℂ) + I * ↑(scale σ p * fderiv ℝ σ p.1 (normal p.2.1)))) = _
    rw [dv]
    simp only [unit,normal,map_add,map_smul,smul_eq_mul]
    simp [U,c,n,sx,sy, -Complex.ofReal_cos,
      -Complex.ofReal_sin, -Complex.ofReal_exp]
    ring
  have lh : L (H σ p) = (scale σ p : ℂ)*W := by
    simp only [L, ContinuousLinearMap.comp_apply, polar_derivative, hμ]
    change D (scale σ p • normal p.2.1, μ * ((0 : ℂ) + I * ↑(scale σ p * fderiv ℝ σ p.1 (-unit p.2.1)))) = _
    rw [dv]
    simp only [unit,normal,map_add,map_smul,map_neg,smul_eq_mul]
    simp [W,c,n,sx,sy, -Complex.ofReal_cos,
      -Complex.ofReal_sin, -Complex.ofReal_exp]
    ring
  have key := coefficients r c n sx sy A B C hn den
  change (1+r^2)*u*(U+I*((1-r^2)/(1+r^2))*W) =
    μ^2*(A-I*B)+(A+I*B) - μ*(μ^2*(sx-I*sy)-(sx+I*sy))*C at key
  simp only [ChartStein.connectionCoefficient, hμ]
  change μ^2*(A-I*B)+(A+I*B) - μ*(μ^2*(sx-I*sy)-(sx+I*sy))*C = 0 ↔ _
  rw [← key, mul_eq_zero, or_iff_right (mul_ne_zero den un), ← rad, lh, lx]
  have hscale : (scale σ p : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_ne_zero (-σ p.1))
  constructor
  · intro q
    linear_combination -(scale σ p : ℂ)*I*q + (scale σ p : ℂ)*(t p : ℂ)*W*Complex.I_sq
  · intro q
    have hh : (scale σ p : ℂ)*(U+I*(t p : ℂ)*W) = 0 := by
      linear_combination I*q + (scale σ p : ℂ)*U*Complex.I_sq
    exact (mul_eq_zero.mp hh).resolve_left hscale

end TransportOkaGrauert.PolarCR
