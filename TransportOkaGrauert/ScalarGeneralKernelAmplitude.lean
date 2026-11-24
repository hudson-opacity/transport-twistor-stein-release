import TransportOkaGrauert.ScalarGeneralKernel
import TransportOkaGrauert.SimpleRadialDivision
import TransportOkaGrauert.ScalarGeneralCauchy
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! # Smoothness of the ray density in radial coordinates at the pole -/

noncomputable section
namespace TransportOkaGrauert.ScalarGeneralKernel
open Complex Metric MeasureTheory Set Filter
open scoped ContDiff Topology

theorem determinant_formula (M : ℂ →L[ℝ] ℂ) :
    M.det = (M 1).re * (M I).im - (M I).re * (M 1).im := by
  change LinearMap.det (M : ℂ →ₗ[ℝ] ℂ) = _
  rw [← LinearMap.det_toMatrix Complex.basisOneI, Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, Complex.coe_basisOneI_repr, Complex.coe_basisOneI]

private theorem determinant_smooth {W : ℂ → ℂ} (sW : ContDiff ℝ ∞ W) :
    ContDiff ℝ ∞ (fun y => (fderiv ℝ W y).det) := by
  simp_rw [determinant_formula]
  have s (v : ℂ) : ContDiff ℝ ∞ (fun y => fderiv ℝ W y v) :=
    (sW.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  exact ((reCLM.contDiff.comp (s 1)).mul (imCLM.contDiff.comp (s I))).sub
    ((reCLM.contDiff.comp (s I)).mul (imCLM.contDiff.comp (s 1)))

def slope (W : ℂ → ℂ) (a : ℂ) (p : ℝ × ℂ) : ℂ :=
  ∫ t in (0:ℝ)..1, fderiv ℝ W (a+t • (p.1 • p.2)) p.2

private theorem slope_smooth {W : ℂ → ℂ} (sW : ContDiff ℝ ∞ W) (a : ℂ) :
    ContDiff ℝ ∞ (slope W a) := by
  apply ScalarGeneralCauchy.integral_smooth (g := fun q : (ℝ × ℂ) × ℝ =>
    fderiv ℝ W (a+q.2 • (q.1.1 • q.1.2)) q.1.2) (T := 1) _ one_pos
  have s : ContDiff ℝ ∞ (fun q : (ℝ × ℂ) × ℝ => a + q.2 • (q.1.1 • q.1.2)) :=
    contDiff_const.add (contDiff_snd.smul ((contDiff_fst.comp contDiff_fst).smul
      (contDiff_snd.comp contDiff_fst)))
  exact ((sW.fderiv_right (m := ∞) (by simp)).comp s).clm_apply (contDiff_snd.comp contDiff_fst)

theorem slope_origin (W : ℂ → ℂ) (a v : ℂ) : slope W a (0,v) = fderiv ℝ W a v := by
  simp [slope]

theorem slope_eq {W : ℂ → ℂ} (sW : ContDiff ℝ ∞ W) (a : ℂ) (r : ℝ) (v : ℂ) :
    r • slope W a (r,v) = W (a+r • v) - W a := by
  let line (t : ℝ) := a+t • (r • v)
  have h (t : ℝ) : HasDerivAt line (r • v) t := by
    simpa only [one_smul] using (((hasDerivAt_id t).smul_const (r • v)).const_add a)
  have d (t : ℝ) : HasDerivAt (W ∘ line) (r • fderiv ℝ W (line t) v) t := by
    simpa only [map_smul] using (sW.differentiable (by simp) (line t)).hasFDerivAt.comp_hasDerivAt t (h t)
  have s : ContDiff ℝ ∞ (W ∘ line) := sW.comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  have E := intervalIntegral.integral_deriv_eq_sub (a := 0) (b := 1) (f := W ∘ line)
    (fun t _ => (d t).differentiableAt) ((s.continuous_deriv (by simp)).intervalIntegrable _ _)
  simp_rw [(d _).deriv] at E
  simpa [slope,line,intervalIntegral.integral_smul] using E

/-- After multiplication by positive geodesic chart radius, the ray density
extends smoothly across every direction over the diagonal. The extended value
is the conformal factor at the centre. -/
theorem Coordinates.radial_amplitude {σ : ℂ → ℝ} {a : ℂ} (C : Coordinates σ a) (ha : ‖a‖ < 1) :
    ∃ A : ℝ × ℂ → ℝ, ∀ v : ℂ, ‖v‖ = 1 →
      ContDiffAt ℝ ∞ A (0,v) ∧ A (0,v) = Real.exp (σ a) ∧
      ∀ᶠ p : ℝ × ℂ in 𝓝 (0,v), 0 < p.1 → p.1 * C.density (a + p.1 • p.2) = A p := by
  have ha' : a ∈ ball (0:ℂ) 1 := mem_ball_zero_iff.mpr ha
  obtain ⟨W,sW,g⟩ := SimpleRadialDivision.extend isOpen_ball isClosed_singleton
    (singleton_subset_iff.mpr ha') C.log_smooth
  have germ := g a (mem_singleton a)
  have grad := germ.fderiv (𝕜 := ℝ)
  have W0 : W a = 0 := germ.self_of_nhds.trans (C.log_zero ha)
  have dW := grad.self_of_nhds.trans (C.log_derivative ha)
  let D (p : ℝ × ℂ) := (fderiv ℝ W (a+p.1 • p.2)).det
  let A (p : ℝ × ℂ) := |D p| / ‖slope W a p‖
  refine ⟨A,fun v hv => ?_⟩
  let c := Real.exp (σ a)
  have hc : 0 < c := Real.exp_pos _
  have s (p : ℝ × ℂ) : ContDiffAt ℝ ∞ D p :=
    ((determinant_smooth sW).comp (contDiff_const.add (contDiff_fst.smul contDiff_snd))).contDiffAt
  have D0 : D (0,v) = c ^ 2 := by
    simp only [D,zero_smul,add_zero,dW]
    change LinearMap.det (c • (LinearMap.id : ℂ →ₗ[ℝ] ℂ)) = _
    rw [LinearMap.det_smul,Complex.finrank_real_complex,LinearMap.det_id,mul_one]
  have n0 : ‖slope W a (0,v)‖ = c := by
    rw [slope_origin,dW]
    simp [hv,c]
  have nonzero : slope W a (0,v) ≠ 0 := norm_ne_zero_iff.mp (n0 ▸ hc.ne')
  refine ⟨?_,?_,?_⟩
  · have smooth_abs : ContDiffAt ℝ ∞ (fun p => |D p|) (0,v) := by
      simpa only [Real.norm_eq_abs] using (s (0,v)).norm ℝ (D0 ▸ (sq_pos_of_pos hc).ne')
    exact smooth_abs.div ((slope_smooth sW a).contDiffAt.norm ℝ nonzero) (n0 ▸ hc.ne')
  · change |D (0,v)| / ‖slope W a (0,v)‖ = c
    rw [D0,abs_of_nonneg (sq_nonneg _), n0]
    field_simp
  · have center : Tendsto (fun p : ℝ × ℂ => a+p.1 • p.2) (𝓝 (0,v)) (𝓝 a) := by
      have h : Continuous (fun p : ℝ × ℂ => a+p.1 • p.2) := continuous_const.add (continuous_fst.smul continuous_snd)
      simpa only [zero_smul,add_zero] using h.tendsto (0,v)
    filter_upwards [center.eventually germ, center.eventually grad] with p hp hd
    intro hr
    have e := slope_eq sW a p.1 p.2
    rw [W0,sub_zero,hp] at e
    change p.1 * (|(fderiv ℝ C.logMap (a+p.1 • p.2)).det| / ‖C.logMap (a+p.1 • p.2)‖) =
      |(fderiv ℝ W (a+p.1 • p.2)).det| / ‖slope W a p‖
    rw [hd, ← e,norm_smul,Real.norm_eq_abs,abs_of_pos hr]
    field_simp

end TransportOkaGrauert.ScalarGeneralKernel
