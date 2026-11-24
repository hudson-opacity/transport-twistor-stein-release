import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# Smooth division for the radial Hessian in dimension two

In local coordinates the radial vector has components `(a,b)`. A symmetric
matrix annihilating that vector is a smooth scalar multiple of the square of
its perpendicular. The smooth scalar extends across the origin, jointly
with every finite-dimensional auxiliary parameter. The proof constructs the
scalar by coordinate division, using the fundamental theorem of calculus.
-/

namespace TransportOkaGrauert.SmoothRadialHessian
noncomputable section

open Filter Metric Set MeasureTheory
open scoped Topology ContDiff Interval

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [ProperSpace P]

private def partialMap {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : P × ℝ → E) (q : P × ℝ) : P →L[ℝ] E :=
  (fderiv ℝ g q).comp (ContinuousLinearMap.inl ℝ P ℝ)

omit [ProperSpace P] in
private theorem smooth_partialMap {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : P × ℝ → E} (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (partialMap g) :=
  (hg.fderiv_right (m := ∞) (by simp)).clm_comp contDiff_const

private theorem integralDerivative {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {g : P × ℝ → E} (hg : ContDiff ℝ ∞ g) (x : P) :
    HasFDerivAt (fun y => ∫ t in (0 : ℝ)..1, g (y,t))
      (∫ t in (0 : ℝ)..1, partialMap g (x,t)) x := by
  have hd := (smooth_partialMap hg).continuous
  have hK := (isCompact_closedBall x 1).prod (isCompact_Icc (a := (0 : ℝ)) (b := 1))
  obtain ⟨C,hC⟩ := hK.bddAbove_image hd.norm.continuousOn
  have slice (y : P) : Continuous (fun t => g (y,t)) :=
    hg.continuous.comp (continuous_const.prodMk continuous_id)
  have dslice : Continuous (fun t => partialMap g (x,t)) :=
    hd.comp (continuous_const.prodMk continuous_id)
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le'' (s := closedBall x 1)
    (F' := fun y t => partialMap g (y,t)) (bound := fun _ => C)
    (closedBall_mem_nhds x zero_lt_one)
  · exact .of_forall fun y => (slice y).aestronglyMeasurable
  · exact (slice x).intervalIntegrable _ _
  · exact dslice.aestronglyMeasurable
  · rw [uIoc_of_le zero_le_one]
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with t ht
    exact fun y hy => hC ⟨(y,t), ⟨hy,Ioc_subset_Icc_self ht⟩, rfl⟩
  · exact intervalIntegrable_const
  · exact .of_forall fun t y _ =>
      ((hg.differentiable (by simp)).differentiableAt.hasFDerivAt.comp y
        ((hasFDerivAt_id y).prodMk (hasFDerivAt_const t y)))

private theorem integralSmoothOrder (n : ℕ) :
    ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
      {g : P × ℝ → E}, ContDiff ℝ ∞ g →
        ContDiff ℝ n (fun x => ∫ t in (0 : ℝ)..1, g (x,t)) := by
  induction n with
  | zero =>
    intro E _ _ _ g hg
    exact contDiff_zero.mpr (continuous_iff_continuousAt.mpr fun x =>
      (integralDerivative hg x).continuousAt)
  | succ n ih =>
    intro E _ _ _ g hg
    exact contDiff_succ_iff_hasFDerivAt.mpr
      ⟨_, ih (smooth_partialMap hg), integralDerivative hg⟩

/-- Hadamard's division lemma at the hyperplane `b = 0`, including all
parameter derivatives. The coefficient is the integral of the last partial
derivative along the segment from `(x,0)` to `(x,b)`. -/
theorem coordinateDivision {f : P × ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hzero : ∀ x, f (x,0) = 0) :
    ∃ c : P × ℝ → ℝ, ContDiff ℝ ∞ c ∧ ∀ x b, f (x,b) = b * c (x,b) := by
  let D (z : P × ℝ) := fderiv ℝ f z (0,1)
  have hD : ContDiff ℝ ∞ D :=
    (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  let g (q : (P × ℝ) × ℝ) := D (q.1.1, q.2 * q.1.2)
  have hg : ContDiff ℝ ∞ g := hD.comp (by fun_prop)
  refine ⟨fun z => ∫ t in (0 : ℝ)..1, g (z,t),
    contDiff_infty.mpr (fun n => integralSmoothOrder n hg), ?_⟩
  intro x b
  have he (t : ℝ) : HasDerivAt (fun t : ℝ => f (x, t*b)) (b * g ((x,b),t)) t := by
    have hpath : HasDerivAt (fun t : ℝ => (x,t*b)) (0,b) t := by
      simpa using (hasDerivAt_const t x).prodMk ((hasDerivAt_id t).mul_const b)
    have h := (hf.differentiable (by simp)).differentiableAt.hasFDerivAt.comp_hasDerivAt t hpath
    have hb : (0,b) = b • ((0,1) : P × ℝ) := by simp [Prod.smul_mk]
    change HasDerivAt _ (b * fderiv ℝ f (x, t*b) (0,1)) t
    rw [show b * fderiv ℝ f (x,t*b) (0,1) = fderiv ℝ f (x,t*b) (0,b) by
      rw [hb, map_smul]; rfl]
    exact h
  have hint : Continuous (fun t => b * g ((x,b),t)) :=
    continuous_const.mul (hg.continuous.comp (continuous_const.prodMk continuous_id))
  have hft := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := 1) (fun t _ => he t) (hint.intervalIntegrable _ _)
  simpa [intervalIntegral.integral_const_mul, hzero] using hft.symm

private theorem acrossOrigin {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ t, t ≠ 0 → f t = g t) (t : ℝ) : f t = g t :=
  congrFun (Continuous.ext_on (dense_compl_singleton (0 : ℝ)) hf hg h) t

/-- A smooth covector that annihilates `(a,b)` has coefficients
`(b*d,-a*d)` for a jointly smooth `d`. In the radial orthonormal frame,
the connection form is therefore `-d` times the dual of the quarter-turn. -/
theorem radialCovectorFactor {l m : (P × ℝ) × ℝ → ℝ}
    (hl : ContDiff ℝ ∞ l) (hm : ContDiff ℝ ∞ m)
    (row : ∀ p a b, l ((p,a),b) * a + m ((p,a),b) * b = 0) :
    ∃ d : (P × ℝ) × ℝ → ℝ, ContDiff ℝ ∞ d ∧ ∀ p a b,
      l ((p,a),b) = b * d ((p,a),b) ∧ m ((p,a),b) = -a * d ((p,a),b) := by
  have lc := hl.continuous
  have mc := hm.continuous
  have lzero (q : P × ℝ) : l (q,0) = 0 := by
    obtain ⟨p,a⟩ := q
    apply acrossOrigin (f := fun t => l ((p,t),0)) (g := fun _ => 0)
      (by fun_prop) continuous_const _ a
    intro t ht
    exact (mul_eq_zero.mp (by simpa using row p t 0)).resolve_right ht
  obtain ⟨d, hd, ld⟩ := coordinateDivision hl lzero
  have dc := hd.continuous
  have md (p : P) (a b : ℝ) : m ((p,a),b) = -a * d ((p,a),b) := by
    apply acrossOrigin (f := fun t => m ((p,a),t)) (g := fun t => -a * d ((p,a),t))
      (by fun_prop) (by fun_prop) _ b
    intro t ht
    apply (mul_right_cancel₀ ht)
    have h := row p a t
    rw [ld] at h
    linear_combination h
  exact ⟨d,hd,fun p a b => ⟨ld (p,a) b,md p a b⟩⟩

/-- Smooth symmetric matrices with radial kernel, in product coordinates.
The parameter `p` may vary together with both vector components. No initial
vanishing order or smooth quotient is assumed. -/
theorem radialKernelFactor {l m n : (P × ℝ) × ℝ → ℝ}
    (hl : ContDiff ℝ ∞ l) (hm : ContDiff ℝ ∞ m) (hn : ContDiff ℝ ∞ n)
    (row₁ : ∀ p a b, l ((p,a),b) * a + m ((p,a),b) * b = 0)
    (row₂ : ∀ p a b, m ((p,a),b) * a + n ((p,a),b) * b = 0) :
    ∃ c : (P × ℝ) × ℝ → ℝ, ContDiff ℝ ∞ c ∧ ∀ p a b,
      l ((p,a),b) = b^2 * c ((p,a),b) ∧
      m ((p,a),b) = -(a*b) * c ((p,a),b) ∧
      n ((p,a),b) = a^2 * c ((p,a),b) := by
  obtain ⟨d,hd,rows⟩ := radialCovectorFactor hl hm row₁
  have dc := hd.continuous
  have nc := hn.continuous
  have dzero (q : P × ℝ) : d (q,0) = 0 := by
    obtain ⟨p,a⟩ := q
    apply acrossOrigin (f := fun t => d ((p,t),0)) (g := fun _ => 0)
      (by fun_prop) continuous_const _ a
    intro t ht
    have h := row₂ p t 0
    rw [(rows p t 0).2] at h
    simpa [ht] using h
  obtain ⟨c,hc,dc'⟩ := coordinateDivision hd dzero
  refine ⟨c,hc,?_⟩
  intro p a b
  refine ⟨by rw [(rows p a b).1, dc']; ring, by rw [(rows p a b).2, dc']; ring, ?_⟩
  apply acrossOrigin (f := fun t => n ((p,a),t)) (g := fun t => a^2 * c ((p,a),t))
    (by fun_prop) ((continuous_const.mul (hc.continuous.comp (continuous_const.prodMk continuous_id)))) _ b
  intro t ht
  apply (mul_right_cancel₀ ht)
  have h := row₂ p a t
  rw [(rows p a t).2, dc'] at h
  linear_combination h

end
end TransportOkaGrauert.SmoothRadialHessian
