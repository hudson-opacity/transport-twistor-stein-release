import TransportOkaGrauert.SimpleDiskTarget
import TransportOkaGrauert.FrameLevi
import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic

/-!
# The geodesic frame for a smooth conformal metric

The coordinates are the complex base point, a lifted angle, and logarithmic velocity
radius. The fields are given by the Levi-Civita connection of exp(2σ)|dz|².
-/

noncomputable section

namespace TransportOkaGrauert.ConformalFrame

open Complex VectorField Filter
open scoped ContDiff

abbrev Chart := ℂ × ℝ × ℝ

def unit (θ : ℝ) : ℂ := Real.cos θ • (1 : ℂ) + Real.sin θ • I

def normal (θ : ℝ) : ℂ := -Real.sin θ • (1 : ℂ) + Real.cos θ • I

private theorem dunit (θ : ℝ) : HasDerivAt unit (normal θ) θ :=
  ((Real.hasDerivAt_cos θ).smul_const (1 : ℂ)).add ((Real.hasDerivAt_sin θ).smul_const I)

private theorem dnormal (θ : ℝ) : HasDerivAt normal (-unit θ) θ := by
  simpa only [unit, normal, neg_smul, neg_add, neg_neg] using
    (((Real.hasDerivAt_sin θ).neg).smul_const (1 : ℂ)).add ((Real.hasDerivAt_cos θ).smul_const I)

def scale (σ : ℂ → ℝ) (p : Chart) := Real.exp (-σ p.1)

private def field (σ : ℂ → ℝ) (u v : ℝ → ℂ) (p : Chart) : Chart :=
  (scale σ p • u p.2.1, scale σ p * fderiv ℝ σ p.1 (v p.2.1), 0)

def X (σ : ℂ → ℝ) := field σ unit normal

def H (σ : ℂ → ℝ) := field σ normal (fun θ => -unit θ)

def V (_ : Chart) : Chart := (0,1,0)

def R (_ : Chart) : Chart := (0,0,1)

private def baseL : Chart →L[ℝ] ℂ := .fst ℝ ℂ (ℝ × ℝ)

private def thetaL : Chart →L[ℝ] ℝ := (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (.snd ℝ ℂ (ℝ × ℝ))

private theorem field_derivative {σ : ℂ → ℝ} (hs : ContDiff ℝ ∞ σ) (u v : ℝ → ℂ)
    {p : Chart} {u' v' : ℂ} (hu : HasDerivAt u u' p.2.1) (hv : HasDerivAt v v' p.2.1) (w : Chart) :
    fderiv ℝ (field σ u v) p w =
      (scale σ p • (w.2.1 • u') + (-(scale σ p * fderiv ℝ σ p.1 w.1)) • u p.2.1,
       scale σ p * (fderiv ℝ σ p.1 (w.2.1 • v') +
          fderiv ℝ (fderiv ℝ σ) p.1 w.1 (v p.2.1)) -
         fderiv ℝ σ p.1 (v p.2.1) * (scale σ p * fderiv ℝ σ p.1 w.1), 0) := by
  have hσ := (hs.differentiable (by simp) p.1).hasFDerivAt.comp p baseL.hasFDerivAt
  have hE := hσ.neg.exp
  have hG := ((hs.fderiv_right (m := ∞) (by simp)).differentiable (by simp) p.1).hasFDerivAt.comp p baseL.hasFDerivAt
  change HasDerivAt u u' (thetaL p) at hu
  change HasDerivAt v v' (thetaL p) at hv
  have hU := hu.hasFDerivAt.comp p thetaL.hasFDerivAt
  have hV := hv.hasFDerivAt.comp p thetaL.hasFDerivAt
  have hd := (hE.smul hU).prodMk ((hE.mul (hG.clm_apply hV)).prodMk (hasFDerivAt_const (0 : ℝ) p))
  rw [show fderiv ℝ (field σ u v) p = _ from hd.fderiv]
  simp [baseL, thetaL, scale, sub_eq_add_neg, mul_comm]
  ring

/-- Contraction of the ordinary real Hessian with a rotated orthonormal pair. -/
private theorem trace_rotated (L : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) (θ : ℝ) :
    L (unit θ) (unit θ) + L (normal θ) (normal θ) = L 1 1 + L I I := by
  simp only [unit, normal, map_add, map_smul, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  linear_combination (L 1 1 + L I I) * Real.sin_sq_add_cos_sq θ

private theorem curvature_eq (σ : ℂ → ℝ) (hs : ContDiff ℝ ∞ σ) (p : Chart) :
    SimpleDiskTarget.curvature σ p.1 =
    -(scale σ p)^2 * ((fderiv ℝ (fderiv ℝ σ) p.1 1) 1 + (fderiv ℝ (fderiv ℝ σ) p.1 I) I) := by
  have hg := (hs.fderiv_right (m := ∞) (by simp)).differentiable (by simp) p.1
  have eig (v : ℂ) : fderiv ℝ (fun z => fderiv ℝ σ z v) p.1 v =
        fderiv ℝ (fderiv ℝ σ) p.1 v v := by
    rw [(hg.hasFDerivAt.clm_apply (hasFDerivAt_const v p.1)).fderiv]
    simp
  simp only [SimpleDiskTarget.curvature, SimpleDiskTarget.laplacian, eig, scale,
    ← Real.exp_nat_mul]
  norm_num

/-- Every smooth conformal factor gives the canonical geodesic bracket relations,
with Gaussian curvature computed from the same Euclidean Laplacian as the Jacobi ODE. -/
theorem brackets {σ : ℂ → ℝ} (hs : ContDiff ℝ ∞ σ) (p : Chart) :
    lieBracket ℝ V (X σ) p = H σ p ∧ lieBracket ℝ (H σ) V p = X σ p ∧
    lieBracket ℝ (X σ) (H σ) p = SimpleDiskTarget.curvature σ p.1 • V p ∧
    lieBracket ℝ (X σ) R p = 0 ∧ lieBracket ℝ R (H σ) p = 0 ∧ lieBracket ℝ R V p = 0 := by
  have dx := field_derivative hs unit normal (p := p) (dunit _) (dnormal _)
  have dh := field_derivative hs normal (fun θ => -unit θ) (p := p) (dnormal _) (dunit _).neg
  change ∀ w, fderiv ℝ (X σ) p w = _ at dx
  change ∀ w, fderiv ℝ (H σ) p w = _ at dh
  have tr := trace_rotated (fderiv ℝ (fderiv ℝ σ) p.1) p.2.1
  have dV : fderiv ℝ V p = 0 := fderiv_const_apply ..
  have dR : fderiv ℝ R p = 0 := fderiv_const_apply ..
  simp only [lieBracket, dx, dh, dV, dR, ContinuousLinearMap.zero_apply]
  simp only [V, R, X, H, field, Prod.smul_mk, Prod.mk_sub_mk, smul_zero,
    zero_sub, sub_zero, map_smul, map_zero, map_neg, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.zero_apply, one_smul, zero_smul, mul_zero, add_zero,
     neg_zero, neg_neg, Prod.mk.injEq, and_true, true_and,
    smul_neg, neg_smul, smul_smul, neg_mul, mul_neg, smul_eq_mul, curvature_eq σ hs p,
    Prod.neg_mk, mul_one, sub_neg_eq_add]
  exact ⟨⟨by abel, by linear_combination -(scale σ p)^2 * tr⟩, rfl, rfl⟩

private def logRadiusL : Chart →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (.snd ℝ ℂ (ℝ × ℝ))

def radialParameter (s : ℝ) : ℝ := (1 - Real.exp (2*s)) / (1 + Real.exp (2*s))

def t (p : Chart) := radialParameter p.2.2

private theorem radial_smooth : ContDiff ℝ ∞ radialParameter := by
  unfold radialParameter
  apply ContDiff.div <;> first | fun_prop | intro a; positivity

private theorem dradial (s : ℝ) : HasDerivAt radialParameter (radialParameter s ^ 2 - 1) s := by
  have he := (((hasDerivAt_id s).const_mul 2).exp)
  have hd := ((hasDerivAt_const s 1).sub he).div ((hasDerivAt_const s 1).add he) (by dsimp; positivity)
  unfold radialParameter
  convert hd using 1
  dsimp
  field_simp [show 1 + Real.exp (2*s) ≠ 0 by positivity]
  ring

private def dualX (σ : ℂ → ℝ) (p : Chart) : Chart →L[ℝ] ℝ :=
  (scale σ p)⁻¹ • (Real.cos p.2.1 • Complex.reCLM.comp baseL + Real.sin p.2.1 • Complex.imCLM.comp baseL)

private def dualH (σ : ℂ → ℝ) (p : Chart) : Chart →L[ℝ] ℝ :=
  (scale σ p)⁻¹ • (-Real.sin p.2.1 • Complex.reCLM.comp baseL + Real.cos p.2.1 • Complex.imCLM.comp baseL)

private def dualV (σ : ℂ → ℝ) (p : Chart) : Chart →L[ℝ] ℝ :=
  thetaL - (X σ p).2.1 • dualX σ p - (H σ p).2.1 • dualH σ p

/-- The transport complex structure in logarithmic polar coordinates on the punctured disk. -/
def J (σ : ℂ → ℝ) (p : Chart) : Chart →L[ℝ] Chart :=
  (dualX σ p).smulRight (t p • H σ p) +
  (dualH σ p).smulRight (-(t p)⁻¹ • X σ p) +
  logRadiusL.smulRight (V p) - (dualV σ p).smulRight (R p)

private theorem dual_horizontal (σ : ℂ → ℝ) (p : Chart) :
    (dualX σ p) (X σ p) = 1 ∧ (dualX σ p) (H σ p) = 0 ∧
    (dualH σ p) (X σ p) = 0 ∧ (dualH σ p) (H σ p) = 1 := by
  have he : scale σ p ≠ 0 := Real.exp_ne_zero _
  simp only [dualX, dualH, X, H, field, unit, normal, baseL, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
    map_smul, map_add, Complex.reCLM_apply, Complex.imCLM_apply, Complex.one_re,
    Complex.one_im, Complex.I_re, Complex.I_im, smul_eq_mul, mul_zero, mul_one, zero_add, add_zero]
  constructor
  · field_simp [he]; linear_combination Real.sin_sq_add_cos_sq p.2.1
  constructor
  · ring
  constructor
  · ring
  · field_simp [he]; linear_combination Real.sin_sq_add_cos_sq p.2.1

theorem complex_frame (σ : ℂ → ℝ) (p : Chart) :
    J σ p (X σ p) = t p • H σ p ∧ J σ p (H σ p) = -(t p)⁻¹ • X σ p ∧
    J σ p (R p) = V p ∧ J σ p (V p) = -R p := by
  obtain ⟨xx,xh,hx,hh⟩ := dual_horizontal σ p
  have xi : (dualX σ p) (R p) = 0 ∧ (dualX σ p) (V p) = 0 := by
    simp [dualX, baseL, R, V]
  have hi : (dualH σ p) (R p) = 0 ∧ (dualH σ p) (V p) = 0 := by
    simp [dualH, baseL, R, V]
  simp only [J, dualV, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smul_apply, xx, xh, hx, hh,
    xi.1, xi.2, hi.1, hi.2, one_smul, zero_smul, smul_eq_mul, mul_zero, mul_one,
    zero_add, add_zero]
  simp [thetaL, logRadiusL, X, H, field, R, V]

theorem smooth_XH {σ : ℂ → ℝ} (hs : ContDiff ℝ ∞ σ) :
    ContDiff ℝ ∞ (X σ) ∧ ContDiff ℝ ∞ (H σ) := by
  have hg := hs.fderiv_right (m := ∞) (by simp)
  have dfield (u v : ℝ → ℂ) (du : ContDiff ℝ ∞ u) (dv : ContDiff ℝ ∞ v) :
      ContDiff ℝ ∞ (field σ u v) := by
    change ContDiff ℝ ∞ (fun p : Chart => (scale σ p • u p.2.1,
      scale σ p * fderiv ℝ σ p.1 (v p.2.1), (0 : ℝ)))
    unfold scale
    fun_prop
  have du : ContDiff ℝ ∞ unit := by unfold unit; fun_prop
  have dv : ContDiff ℝ ∞ normal := by unfold normal; fun_prop
  exact ⟨dfield _ _ du dv, dfield _ _ dv du.neg⟩

/-- The concrete frame over a smooth conformal disk. -/
def frame (σ : ℂ → ℝ) : FrameLevi.Frame Chart where
  X := X σ
  H := H σ
  R := R
  V := V
  J := J σ
  t := t
  K p := SimpleDiskTarget.curvature σ p.1

/-- Every point with log-radius below zero satisfies all the analytic and algebraic
inputs of the exterior-derivative computation. -/
theorem equationsAt {σ : ℂ → ℝ} (hs : ContDiff ℝ ∞ σ) (p : Chart) (hp : p.2.2 < 0) :
    FrameLevi.EquationsAt (frame σ) p := by
  have ht : 0 < t p := by
    have hlt : Real.exp (2*p.2.2) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    exact div_pos (sub_pos.mpr hlt) (by positivity)
  obtain ⟨hx,hh⟩ := smooth_XH hs
  have dt : ContDiff ℝ ∞ t := radial_smooth.comp (contDiff_snd.comp contDiff_snd)
  have he : ContDiff ℝ ∞ (scale σ) := (hs.comp contDiff_fst).neg.exp
  have dxi : ContDiff ℝ ∞ (dualX σ) := by
    unfold dualX
    exact (he.inv fun _ => Real.exp_ne_zero _).smul (by fun_prop)
  have dhi : ContDiff ℝ ∞ (dualH σ) := by
    unfold dualH
    exact (he.inv fun _ => Real.exp_ne_zero _).smul (by fun_prop)
  have dvi : ContDiff ℝ ∞ (dualV σ) :=
    (contDiff_const.sub ((contDiff_fst.comp (contDiff_snd.comp hx)).smul dxi)).sub
      ((contDiff_fst.comp (contDiff_snd.comp hh)).smul dhi)
  have dj : ContDiffAt ℝ ∞ (J σ) p :=
    (((dxi.contDiffAt.smulRight (dt.smul hh).contDiffAt).add
       (dhi.contDiffAt.smulRight ((dt.contDiffAt.inv ht.ne').neg.smul hx.contDiffAt))).add
       (contDiffAt_const.smulRight (contDiffAt_const (c := V p)))).sub
       (dvi.contDiffAt.smulRight (contDiffAt_const (c := R p)))
  obtain ⟨bVX,bHV,bXH,bXR,bRH,bRV⟩ := brackets hs p
  have der (Q : Chart → Chart) (y : Chart) :
      FrameLevi.along Q t y = (t y ^ 2 - 1) * (Q y).2.2 := by
    have ha : HasDerivAt radialParameter (t y ^ 2 - 1) (logRadiusL y) := dradial y.2.2
    exact congrArg (fun L : Chart →L[ℝ] ℝ => L (Q y)) (ha.comp_hasFDerivAt y logRadiusL.hasFDerivAt).fderiv
  refine ⟨(hx.differentiable (by simp)) p, (hh.differentiable (by simp)) p,
    differentiableAt_const _, differentiableAt_const _, dj.differentiableAt (by simp),
    dt.contDiffAt.of_le (by decide), ht,
    .of_forall fun y => (complex_frame σ y).1,
    .of_forall fun y => (complex_frame σ y).2.1,
    .of_forall fun y => (complex_frame σ y).2.2.1,
    .of_forall fun y => (complex_frame σ y).2.2.2, ?_, ?_, ?_, ?_, bXH,bVX,bHV,bXR,bRH,bRV⟩
  · exact .of_forall fun y => by simpa [frame, X, field] using der (X σ) y
  · exact .of_forall fun y => by simpa [frame, H, field] using der (H σ) y
  · exact .of_forall fun y => by simpa [frame, V] using der V y
  · exact .of_forall fun y => by simpa [frame, R] using der R y

/-- The polar-frame potential is exactly the logarithmic velocity barrier. -/
theorem radial_potential (s : ℝ) (hs : s < 0) :
    FrameLevi.radial (radialParameter s) = -Real.log (1 - (Real.exp s)^2) := by
  let e := Real.exp (2*s)
  have he : 0 < e := Real.exp_pos _
  have he' : e < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have heq : (Real.exp s)^2 = e := by rw [← Real.exp_nat_mul]; rfl
  have pos : 0 < 1-e := sub_pos.mpr he'
  have hplus : 0 < 1+e := by linarith
  have eqn : 1 + (1-e)/(1+e) = 2/(1+e) := by field_simp; ring
  change Real.log (1 + (1-e)/(1+e)) - Real.log ((1-e)/(1+e)) - Real.log 2 = _
  rw [eqn, Real.log_div (by norm_num) hplus.ne', Real.log_div pos.ne' hplus.ne', heq]
  ring

private theorem decomposition (σ : ℂ → ℝ) (p w : Chart) :
    w = (dualX σ p w) • X σ p + (dualH σ p w) • H σ p + w.2.2 • R p + (dualV σ p w) • V p := by
  have he : scale σ p ≠ 0 := Real.exp_ne_zero _
  obtain ⟨z,θ,s⟩ := w
  apply Prod.ext
  · apply Complex.ext <;>
      simp [dualX,dualH,X,H,field,unit,normal,baseL,R,V, Complex.mul_re, Complex.mul_im, -Complex.ofReal_cos, -Complex.ofReal_sin] <;>
      field_simp [he] <;>
      first | linear_combination -z.re * Real.sin_sq_add_cos_sq p.2.1 |
              linear_combination -z.im * Real.sin_sq_add_cos_sq p.2.1
  · apply Prod.ext
    · simp [dualV, thetaL, R, V]; ring
    · simp [X,H,field,R,V]

/-- Complex linearity can be tested on one horizontal and one vertical generator. -/
theorem intertwines_iff (σ : ℂ → ℝ) (p : Chart) (ht : t p ≠ 0) (L : Chart →L[ℝ] ℂ) :
    (∀ w, L (J σ p w) = I * L w) ↔
      L (V p) = I * L (R p) ∧ (t p : ℂ) * L (H σ p) = I * L (X σ p) := by
  obtain ⟨jx,jh,jr,jv⟩ := complex_frame σ p
  constructor
  · intro h
    exact ⟨jr ▸ h (R p), by simpa [jx, Complex.real_smul] using h (X σ p)⟩
  · rintro ⟨hv,hx⟩ w
    have hh : -(t p : ℂ)⁻¹ * L (X σ p) = I * L (H σ p) := by
      have htc : (t p : ℂ) ≠ 0 := by exact_mod_cast ht
      field_simp [htc]
      linear_combination -I * hx - L (X σ p) * Complex.I_sq
    rw [decomposition σ p w] 
    simp only [map_add, map_smul, jx, jh, jr, jv, map_neg, Complex.real_smul,
      Complex.ofReal_neg, Complex.ofReal_inv, hh, hx, hv]
    linear_combination -(dualV σ p w : ℂ) * L (R p) * Complex.I_sq

/-- The Schur test implies strict Levi positivity on the entire tangent space of the
concrete chart for every smooth conformal metric. -/
theorem positive_of_schur {σ : ℂ → ℝ} (hs : ContDiff ℝ ∞ σ) (p : Chart) (hp : p.2.2 < 0)
    {h : Chart → ℝ} (dh : ContDiffAt ℝ 2 h p)
    (rh : ∀ᶠ y in nhds p, FrameLevi.along R h y = 0)
    (hB : 0 < LeviBoundary.vertical (t p) (FrameLevi.jet (frame σ) h p))
    (hS : 0 < LeviBoundary.schur (t p) (FrameLevi.jet (frame σ) h p))
    {w : Chart} (hw : w ≠ 0) :
    0 < FrameLevi.ddC (J σ) (FrameLevi.potential (frame σ) h) p w (J σ p w) := by
  have q := equationsAt hs p hp
  have ht : t p ≠ 0 := q.positive.ne'
  apply FrameLevi.positive_of_schur q dh rh hB hS (dualX σ p w) (dualH σ p w / t p)
    w.2.2 (dualV σ p w) _ hw
  change w = _ • X σ p + _ • J σ p (X σ p) + _ • R p + _ • J σ p (R p)
  rw [(complex_frame σ p).1, (complex_frame σ p).2.2.1, smul_smul, div_mul_cancel₀ _ ht]
  exact decomposition σ p w

end TransportOkaGrauert.ConformalFrame
