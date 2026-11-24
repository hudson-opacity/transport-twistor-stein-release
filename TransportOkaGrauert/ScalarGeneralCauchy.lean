import TransportOkaGrauert.SmoothCoefficient
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Integral.CircleIntegral

/-! A polar Cauchy–Green primitive on the closed disk. The radial and angular
integrals have fixed finite limits, so all ambient base derivatives are smooth. -/
noncomputable section
namespace TransportOkaGrauert.ScalarGeneralCauchy
open Complex Metric MeasureTheory Set Filter
open scoped ContDiff Topology Interval ComplexConjugate

section Integral
variable {B F : Type} [NormedAddCommGroup B] [NormedSpace ℝ B] [ProperSpace B]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

private def baseD (g : B × ℝ → F) (p : B × ℝ) : B →L[ℝ] F :=
  (fderiv ℝ g p).comp (ContinuousLinearMap.inl ℝ B ℝ)

omit [ProperSpace B] [CompleteSpace F] in
private theorem partial_smooth {g : B × ℝ → F} (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (baseD g) :=
  (hg.fderiv_right (m := ∞) (by simp)).clm_comp contDiff_const

omit [CompleteSpace F] in
private theorem integral_partial {g : B × ℝ → F} (hg : ContDiff ℝ ∞ g) (x : B)
    {T : ℝ} (hT : 0 < T) :
    HasFDerivAt (fun y => ∫ t in (0 : ℝ)..T, g (y,t))
      (∫ t in (0 : ℝ)..T, baseD g (x,t)) x := by
  have hc := (partial_smooth hg).continuous
  obtain ⟨C,hC⟩ := ((isCompact_closedBall x 1).prod (isCompact_Icc (a := (0:ℝ)) (b := T))).bddAbove_image
    hc.norm.continuousOn
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le'' (s := closedBall x 1)
    (F' := fun y t => baseD g (y,t)) (bound := fun _ => C) (closedBall_mem_nhds x one_pos)
  · exact Eventually.of_forall fun y => (hg.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact (hg.continuous.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
  · exact (hc.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · rw [uIoc_of_le hT.le]
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with t ht
    intro y hy
    exact hC ⟨(y,t), ⟨hy, Ioc_subset_Icc_self ht⟩, rfl⟩
  · exact intervalIntegrable_const
  · exact Eventually.of_forall fun t y _ => (hg.differentiable (by simp) (y,t)).hasFDerivAt.comp y
      ((hasFDerivAt_id y).prodMk (hasFDerivAt_const t y))

private theorem integral_smooth_order (m : ℕ) : ∀ (F : Type) [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] (g : B × ℝ → F) {T : ℝ}, 0 < T → ContDiff ℝ ∞ g →
      ContDiff ℝ m (fun y => ∫ t in (0 : ℝ)..T, g (y,t)) := by
  induction m with
  | zero =>
    intro F _ _ _ g T hT hg
    exact contDiff_zero.mpr (continuous_iff_continuousAt.mpr fun x => (integral_partial hg x hT).continuousAt)
  | succ m ih =>
    intro F _ _ _ g T hT hg
    apply (contDiff_succ_iff_fderiv (n := (m : WithTop ℕ∞))).mpr
    refine ⟨fun x => (integral_partial hg x hT).differentiableAt, by simp, ?_⟩
    have h := ih (B →L[ℝ] F) (baseD g) hT (partial_smooth hg)
    rw [show fderiv ℝ (fun y => ∫ t in (0:ℝ)..T, g (y,t)) = _ from funext fun x => (integral_partial hg x hT).fderiv]
    exact h

/-- Integrating a jointly smooth family on a fixed compact interval preserves every derivative. -/
theorem integral_smooth {g : B × ℝ → F} (hg : ContDiff ℝ ∞ g) {T : ℝ} (hT : 0 < T) :
    ContDiff ℝ ∞ (fun y => ∫ t in (0 : ℝ)..T, g (y,t)) :=
  contDiff_infty.mpr fun m => integral_smooth_order m F g hT hg

omit [CompleteSpace F] in
/-- A base derivative commutes with the fixed-interval integral of a smooth family. -/
theorem integral_direction {g : B × ℝ → F} (hg : ContDiff ℝ ∞ g) (x v : B)
    {T : ℝ} (hT : 0 < T) :
    fderiv ℝ (fun y => ∫ t in (0 : ℝ)..T, g (y,t)) x v =
      ∫ t in (0 : ℝ)..T, fderiv ℝ (fun y => g (y,t)) x v := by
  have hi : IntervalIntegrable (fun t => baseD g (x,t)) volume 0 T :=
    ((partial_smooth hg).continuous.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
  rw [(integral_partial hg x hT).fderiv, ContinuousLinearMap.intervalIntegral_apply hi]
  apply intervalIntegral.integral_congr
  intro t _
  have hp : HasFDerivAt (fun y : B => (y,t)) (ContinuousLinearMap.inl ℝ B ℝ) x :=
    (hasFDerivAt_id _).prodMk (hasFDerivAt_const _ _)
  have h : HasFDerivAt (fun y => g (y,t)) (baseD g (x,t)) x :=
    (hg.differentiable (by simp) (x,t)).hasFDerivAt.comp x hp
  exact congrArg (fun L : B →L[ℝ] F => L v) h.fderiv.symm
end Integral

private abbrev period := 2 * Real.pi
private def unit (t : ℝ) : ℂ := circleMap 0 1 t
private theorem smooth_unit : ContDiff ℝ ∞ unit := contDiff_circleMap 0 1
private theorem deriv_unit (t : ℝ) : HasDerivAt unit (unit t * I) t := hasDerivAt_circleMap _ _ _

/-- Twice the anti-holomorphic Wirtinger derivative, evaluated as a real-linear
functional on the ordinary Fréchet derivative. -/
def twiceBar : (ℂ →L[ℝ] ℂ) →L[ℝ] ℂ :=
  ContinuousLinearMap.apply ℝ ℂ 1 + I • ContinuousLinearMap.apply ℝ ℂ I

private theorem rotation (L : ℂ →L[ℝ] ℂ) (e : ℂ) :
    conj e * twiceBar L = L e + I * L (e * I) := by
  have split (v : ℂ) : L v = (v.re : ℂ) * L 1 + (v.im : ℂ) * L I := by
    have hv : v = v.re • (1 : ℂ) + v.im • I := by simp [Complex.real_smul]
    conv_lhs => rw [hv,map_add,map_smul,map_smul]
    rfl
  rw [split e, split (e * I)]
  change conj e * (L 1 + I * L I) = _
  simp only [Complex.mul_I_re, Complex.mul_I_im, Complex.ofReal_neg]
  have he : conj e = (e.re : ℂ) - (e.im : ℂ) * I := by apply Complex.ext <;> simp
  rw [he]
  ring_nf
  simp [Complex.I_sq]
  ring

private def mean (f : ℂ → ℂ) (z : ℂ) (r : ℝ) : ℂ :=
  ∫ t in (0:ℝ)..period, f (z + (r:ℂ) * unit t)

private def weighted (f : ℂ → ℂ) (p : ℂ × ℝ) : ℂ :=
  ∫ t in (0:ℝ)..period, conj (unit t) * f (p.1 + (p.2:ℂ) * unit t)

private theorem weighted_smooth {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (weighted f) := by
  apply integral_smooth (g := fun p : (ℂ × ℝ) × ℝ => conj (unit p.2) * f (p.1.1 + (p.1.2 : ℂ)*unit p.2)) _ Real.two_pi_pos
  exact (Complex.conjCLE.contDiff.comp (smooth_unit.comp contDiff_snd)).mul
    (hf.comp ((contDiff_fst.comp contDiff_fst).add
      ((Complex.ofRealCLM.contDiff.comp (contDiff_snd.comp contDiff_fst)).mul (smooth_unit.comp contDiff_snd))))

private theorem mean_smooth {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f) (z : ℂ) : ContDiff ℝ ∞ (mean f z) := by
  apply integral_smooth (g := fun p : ℝ × ℝ => f (z + (p.1 : ℂ)*unit p.2)) _ Real.two_pi_pos
  exact hf.comp (contDiff_const.add ((Complex.ofRealCLM.contDiff.comp contDiff_fst).mul (smooth_unit.comp contDiff_snd)))

private theorem mean_deriv {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f) (z : ℂ) (r : ℝ) :
    deriv (mean f z) r = ∫ t in (0:ℝ)..period, fderiv ℝ f (z + (r:ℂ) * unit t) (unit t) := by
  let g (p : ℝ × ℝ) := f (z + (p.1:ℂ) * unit p.2)
  have hg : ContDiff ℝ ∞ g := hf.comp (contDiff_const.add
    ((Complex.ofRealCLM.contDiff.comp contDiff_fst).mul (smooth_unit.comp contDiff_snd)))
  rw [← fderiv_apply_one_eq_deriv]
  change fderiv ℝ (fun s => ∫ t in (0:ℝ)..period, g (s,t)) r 1 = _
  rw [integral_direction hg _ _ Real.two_pi_pos]
  apply intervalIntegral.integral_congr; intro t _
  dsimp only
  rw [fderiv_apply_one_eq_deriv]
  apply HasDerivAt.deriv
  apply (hf.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt r
  simpa using (((Complex.ofRealCLM.hasDerivAt (x := r)).mul_const (unit t)).const_add z)

private theorem twiceBar_integral {g : ℂ × ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (z : ℂ)
    {T : ℝ} (hT : 0 < T) :
    twiceBar (fderiv ℝ (fun y => ∫ t in (0:ℝ)..T, g (y,t)) z) =
      ∫ t in (0:ℝ)..T, twiceBar (fderiv ℝ (fun y => g (y,t)) z) := by
  have hi : IntervalIntegrable (fun t => baseD g (z,t)) volume 0 T :=
    ((partial_smooth hg).continuous.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
  rw [(integral_partial hg z hT).fderiv, ← twiceBar.intervalIntegral_comp_comm hi]
  apply intervalIntegral.integral_congr; intro t _
  apply congrArg twiceBar
  exact ((hg.differentiable (by simp) (z,t)).hasFDerivAt.comp z
    ((hasFDerivAt_id z).prodMk (hasFDerivAt_const t z))).fderiv.symm


private theorem angular_cancel {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f) (z : ℂ) {r : ℝ} (hr : 0 < r) :
    (∫ t in (0:ℝ)..period, fderiv ℝ f (z + (r:ℂ) * unit t) (unit t * I)) = 0 := by
  let h (t : ℝ) := f (z + (r:ℂ) * unit t)
  have hs : ContDiff ℝ ∞ h := hf.comp (contDiff_const.add (contDiff_const.mul smooth_unit))
  have hd (t : ℝ) : deriv h t = (r:ℂ) * fderiv ℝ f (z + (r:ℂ) * unit t) (unit t * I) := by
    have H := (hf.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt t
      (((deriv_unit t).const_mul (r:ℂ)).const_add z)
    change deriv h t = _
    change HasDerivAt h _ t at H
    rw [H.deriv]
    exact (fderiv ℝ f _).map_smul r (unit t * I)
  have ends : h period = h 0 := by simp [h, unit, circleMap, period, Complex.exp_two_pi_mul_I]
  have he := intervalIntegral.integral_deriv_eq_sub (a := 0) (b := period) (f := h)
    (fun t _ => hs.differentiable (by simp) t) ((hs.continuous_deriv (by simp)).intervalIntegrable _ _)
  simp_rw [hd] at he
  rw [intervalIntegral.integral_const_mul, ends, sub_self] at he
  exact (mul_eq_zero.mp he).resolve_left (Complex.ofReal_ne_zero.mpr hr.ne')

private theorem twiceBar_const_mul (c : ℂ) (L : ℂ →L[ℝ] ℂ) :
    twiceBar (c • L) = c * twiceBar L := by
  change c * L 1 + I * (c * L I) = c * (L 1 + I * L I)
  ring

/-- The first angular moment converts the Wirtinger derivative in the centre
into a radial derivative of the circular mean. -/
private theorem moment_identity {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f) (z : ℂ) {r : ℝ} (hr : 0 < r) :
    twiceBar (fderiv ℝ (fun y => weighted f (y,r)) z) = deriv (mean f z) r := by
  let g (p : ℂ × ℝ) := conj (unit p.2) * f (p.1 + (r:ℂ) * unit p.2)
  have hg : ContDiff ℝ ∞ g := (Complex.conjCLE.contDiff.comp (smooth_unit.comp contDiff_snd)).mul
    (hf.comp (contDiff_fst.add (contDiff_const.mul (smooth_unit.comp contDiff_snd))))
  change twiceBar (fderiv ℝ (fun y => ∫ t in (0:ℝ)..period, g (y,t)) z) = _
  rw [twiceBar_integral hg _ Real.two_pi_pos, mean_deriv hf]
  let D (t : ℝ) := fderiv ℝ f (z + (r:ℂ) * unit t)
  have hc : Continuous D := (hf.continuous_fderiv (by simp)).comp
    (continuous_const.add (continuous_const.mul smooth_unit.continuous))
  have hre : IntervalIntegrable (fun t => D t (unit t)) volume 0 period :=
    (hc.clm_apply smooth_unit.continuous).intervalIntegrable _ _
  have him : IntervalIntegrable (fun t => I * D t (unit t * I)) volume 0 period :=
    (continuous_const.mul (hc.clm_apply (smooth_unit.continuous.mul continuous_const))).intervalIntegrable _ _
  have at_t (t : ℝ) : twiceBar (fderiv ℝ (fun y => g (y,t)) z) = D t (unit t) + I * D t (unit t * I) := by
    have hd : HasFDerivAt (fun y => f (y + (r:ℂ) * unit t)) (D t) z :=
      (hf.differentiable (by simp) _).hasFDerivAt.comp z ((hasFDerivAt_id z).add_const _)
    have hm : HasFDerivAt (fun y => g (y,t)) (conj (unit t) • D t) z := hd.const_mul (conj (unit t))
    rw [hm.fderiv, twiceBar_const_mul, rotation]
  simp_rw [at_t]
  rw [intervalIntegral.integral_add hre him, intervalIntegral.integral_const_mul,
    show (∫ t in (0:ℝ)..period, D t (unit t * I)) = 0 from angular_cancel hf z hr, mul_zero, add_zero]

private def rawPrimitive (f : ℂ → ℂ) (z : ℂ) : ℂ := ∫ r in (0:ℝ)..4, weighted f (z,r)

private theorem rawPrimitive_identity {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f) (z : ℂ) :
    twiceBar (fderiv ℝ (rawPrimitive f) z) = mean f z 4 - (period:ℂ) * f z := by
  unfold rawPrimitive
  rw [twiceBar_integral (weighted_smooth hf) z (by norm_num : (0:ℝ) < 4)]
  have he : (∫ r in (0:ℝ)..4, twiceBar (fderiv ℝ (fun y => weighted f (y,r)) z)) =
      ∫ r in (0:ℝ)..4, deriv (mean f z) r := by
    apply intervalIntegral.integral_congr_ae
    exact Eventually.of_forall fun r hr => moment_identity hf z ((uIoc_of_le (by norm_num : (0:ℝ) ≤ 4)) ▸ hr).1
  rw [he, intervalIntegral.integral_deriv_eq_sub (fun r _ => (mean_smooth hf z).differentiable (by simp) r)
    (((mean_smooth hf z).continuous_deriv (by simp)).intervalIntegrable _ _)]
  simp [mean, Complex.real_smul]

/-- For every smooth complex datum there is a globally smooth primitive of
`∂ₓ + i∂ᵧ` on the entire closed unit disk. The cutoff is fixed independently of the datum. -/
theorem exists_twiceBar_primitive (f : ℂ → ℂ) (hf : ContDiff ℝ ∞ f) :
    ∃ u : ℂ → ℂ, ContDiff ℝ ∞ u ∧ ∀ z ∈ closedBall (0:ℂ) 1, twiceBar (fderiv ℝ u z) = f z := by
  let χ : ContDiffBump (0:ℂ) := ⟨1, 2, by norm_num, by norm_num⟩
  let g (z : ℂ) := (χ z : ℂ) * f z
  have hg : ContDiff ℝ ∞ g := (Complex.ofRealCLM.contDiff.comp χ.contDiff).mul hf
  have hs : ContDiff ℝ ∞ (rawPrimitive g) := integral_smooth (weighted_smooth hg) (by norm_num : (0:ℝ) < 4)
  refine ⟨fun z => -(period:ℂ)⁻¹ * rawPrimitive g z, contDiff_const.mul hs, ?_⟩
  intro z hz
  have boundary (t : ℝ) : g (z + (4:ℂ)*unit t) = 0 := by
    have hunit : ‖unit t‖ = 1 := by simp [unit, circleMap, Complex.norm_exp_ofReal_mul_I]
    have ha := norm_sub_norm_le ((4:ℂ)*unit t) (-z)
    rw [norm_mul, hunit, mul_one, norm_neg, sub_neg_eq_add, add_comm] at ha
    have hn : (2:ℝ) ≤ ‖z + (4:ℂ)*unit t‖ := by
      have := mem_closedBall_zero_iff.mp hz
      norm_num at ha
      linarith
    have hout : χ (z + (4:ℂ)*unit t) = 0 := χ.zero_of_le_dist (by simpa [dist_zero_right, χ] using hn)
    simp [g,hout]
  have hm : mean g z 4 = 0 := by simp [mean,boundary]
  have H := ((hs.differentiable (by simp) z).hasFDerivAt.const_mul (-(period:ℂ)⁻¹)).fderiv
  rw [H, twiceBar_const_mul, rawPrimitive_identity hg, hm, zero_sub]
  have hχ : χ z = 1 := χ.one_of_mem_closedBall hz
  have hp : (period:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.two_pi_pos.ne'
  simp only [g,hχ, Complex.ofReal_one, one_mul, neg_mul_neg, ← mul_assoc, inv_mul_cancel₀ hp]

end TransportOkaGrauert.ScalarGeneralCauchy
