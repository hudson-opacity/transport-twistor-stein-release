import TransportOkaGrauert.ChartRegularity
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.MeanValue

/-! # A complete extension of the lifted geodesic vector field

Cut off the conformal factor beyond a neighborhood of the closed unit disk.
The resulting metric is Euclidean at infinity. Its lifted geodesic vector and
its first derivative attain all their values on a compact fundamental cylinder.
-/

noncomputable section
namespace TransportOkaGrauert.GeodesicFlowExtension

open PathContinuation Metric Set Filter Complex
open scoped ContDiff Topology NNReal

abbrev State := ℂ × ℝ

private def cutoff : ContDiffBump (0 : ℂ) := ⟨2, 3, by norm_num, by norm_num⟩

def extendedFactor (σ : ℂ → ℝ) (z : ℂ) := cutoff z * σ z

def extended (σ : ℂ → ℝ) := chartVector (extendedFactor σ)

theorem factor_smooth {σ : ℂ → ℝ} (hs : ContDiff ℝ ∞ σ) : ContDiff ℝ ∞ (extendedFactor σ) :=
  cutoff.contDiff.mul hs

theorem factor_eq {σ : ℂ → ℝ} {z : ℂ} (hz : ‖z‖ < 2) :
    extendedFactor σ =ᶠ[𝓝 z] σ := by
  have h := cutoff.eventuallyEq_one_of_mem_ball (x := z) (by simpa [cutoff] using hz)
  filter_upwards [h] with y hy
  simp [extendedFactor, hy]

theorem factor_flat {σ : ℂ → ℝ} {z : ℂ} (hz : 3 < ‖z‖) :
    extendedFactor σ =ᶠ[𝓝 z] 0 := by
  filter_upwards [continuous_norm.continuousAt.eventually_const_lt hz] with y hy
  have h := cutoff.zero_of_le_dist (x := y) (by simpa [cutoff] using hy.le)
  simp [extendedFactor, h]

private theorem chart_congr {σ τ : ℂ → ℝ} {p : State} (h : σ =ᶠ[𝓝 p.1] τ) :
    chartVector σ p = chartVector τ p := by
  simp only [chartVector, Isothermal.angularDrift, h.fderiv_eq, h.eq_of_nhds]

theorem agrees {σ : ℂ → ℝ} {p : State} (hp : ‖p.1‖ < 2) :
    extended σ p = chartVector σ p := chart_congr (factor_eq hp)

theorem flat {σ : ℂ → ℝ} {p : State} (hp : 3 < ‖p.1‖) :
    extended σ p = ((Circle.exp p.2 : ℂ), 0) := by
  rw [extended, chart_congr (factor_flat hp)]
  simp [chartVector, Isothermal.angularDrift]

theorem smooth {σ : ℂ → ℝ} (hs : ContDiff ℝ ∞ σ) : ContDiff ℝ ∞ (extended σ) :=
  contDiff_iff_contDiffAt.mpr fun p => ChartRegularity.chartVector_contDiffAt p (factor_smooth hs).contDiffAt

private theorem translation_jet {F : State → State} (hF : Differentiable ℝ F) (p a : State)
    (hg : (fun y => F (y+a)) =ᶠ[𝓝 p] F) :
    F (p+a) = F p ∧ fderiv ℝ F (p+a) = fderiv ℝ F p := by
  have d := (hF (p+a)).hasFDerivAt.comp p ((hasFDerivAt_id p).add_const a)
  change HasFDerivAt (fun y => F (y+a)) _ p at d
  exact ⟨hg.eq_of_nhds, by simpa using d.fderiv.symm.trans hg.fderiv_eq⟩

private theorem field_flat {σ : ℂ → ℝ} {c r : ℝ} (outside : ∀ z : ℂ, r < ‖z‖ → σ z = c)
    {p : State} (hp : r < ‖p.1‖) :
    chartVector σ p = Real.exp (-c) • ((Circle.exp p.2 : ℂ), (0 : ℝ)) := by
  have hg : σ =ᶠ[𝓝 p.1] fun _ => c := by
    filter_upwards [continuous_norm.continuousAt.eventually_const_lt hp] with z hz
    exact outside z hz
  rw [chart_congr hg]
  simp [chartVector, Isothermal.angularDrift]

private theorem representative {σ : ℂ → ℝ} (hs : ContDiff ℝ ∞ σ) {c r R : ℝ}
    (hr : r < R) (hR : 0 ≤ R) (outside : ∀ z : ℂ, r < ‖z‖ → σ z = c) (p : State) :
    ∃ q ∈ closedBall (0 : ℂ) R ×ˢ Icc (-Real.pi) Real.pi,
      chartVector σ q = chartVector σ p ∧ fderiv ℝ (chartVector σ) q = fderiv ℝ (chartVector σ) p := by
  let θ := (Circle.exp p.2 : ℂ).arg
  let x : ℂ := if ‖p.1‖ ≤ R then p.1 else (R : ℂ)
  let a : State := (x-p.1, θ-p.2)
  have eq : p+a = (x,θ) := by ext <;> simp [a]
  have expθ : Circle.exp θ = Circle.exp p.2 := Circle.exp_arg _
  have expShift (t : ℝ) : Circle.exp (t + a.2) = Circle.exp t := by
    simp [a, sub_eq_add_neg, Circle.exp_add, Circle.exp_neg, expθ]
  have d : Differentiable ℝ (chartVector σ) := fun y =>
    (ChartRegularity.chartVector_contDiffAt y hs.contDiffAt).differentiableAt (by simp)
  have germ : (fun y => chartVector σ (y+a)) =ᶠ[𝓝 p] chartVector σ := by
    by_cases hi : ‖p.1‖ ≤ R
    · exact Eventually.of_forall fun y => by
        have hbase : (y+a).1 = y.1 := by simp [a,x,hi]
        simp only [chartVector, hbase, Prod.snd_add, expShift]
    · have ho := hr.trans (lt_of_not_ge hi)
      have hx : r < ‖(p+a).1‖ := by simpa [eq,x,hi,abs_of_nonneg hR] using hr
      have h₁ : Continuous (fun y : State => ‖(y+a).1‖) := by fun_prop
      filter_upwards [(continuous_fst.norm.continuousAt (x := p)).eventually_const_lt ho,
        h₁.continuousAt.eventually_const_lt hx] with y hy hy'
      simp only [field_flat outside hy, field_flat outside hy', Prod.snd_add, expShift]
  refine ⟨(x,θ), ⟨?_, ⟨(Complex.neg_pi_lt_arg _).le, Complex.arg_le_pi _⟩⟩, ?_⟩
  · by_cases H : ‖p.1‖ ≤ R <;> simp [x,H,abs_of_nonneg hR]
  · rw [← eq]
    exact translation_jet d p a germ

/-- A smooth conformal metric constant near infinity has globally bounded
geodesic speed and globally bounded first derivative on the angle cover. -/
theorem bounds_of_constant_exterior {σ : ℂ → ℝ} (hs : ContDiff ℝ ∞ σ) {r c : ℝ}
    (outside : ∀ z : ℂ, r < ‖z‖ → σ z = c) :
    ∃ B : ℝ≥0, ∀ p, ‖chartVector σ p‖ ≤ B ∧ ‖fderiv ℝ (chartVector σ) p‖ ≤ B := by
  let R := max (r+1) 1
  have hr : r < R := (lt_add_one r).trans_le (le_max_left ..)
  have hR : 0 ≤ R := zero_le_one.trans (le_max_right ..)
  let K := closedBall (0 : ℂ) R ×ˢ Icc (-Real.pi) Real.pi
  have hc : IsCompact K := (isCompact_closedBall (0 : ℂ) R).prod isCompact_Icc
  have hne : K.Nonempty := ⟨(0,0), by simp [K,hR,Real.pi_pos.le]⟩
  let f := fun p : State => max ‖chartVector σ p‖ ‖fderiv ℝ (chartVector σ) p‖
  have d : ContDiff ℝ ∞ (chartVector σ) :=
    contDiff_iff_contDiffAt.mpr fun p => ChartRegularity.chartVector_contDiffAt p hs.contDiffAt
  have hf : Continuous f := d.continuous.norm.max (d.continuous_fderiv (by simp)).norm
  obtain ⟨m, _, hm⟩ := hc.exists_isMaxOn hne hf.continuousOn
  refine ⟨⟨f m, le_max_of_le_left (norm_nonneg _)⟩, fun p => ?_⟩
  obtain ⟨q,hq,eq,dq⟩ := representative hs hr hR outside p
  exact ⟨eq ▸ (le_max_left ..).trans (isMaxOn_iff.mp hm q hq),
    dq ▸ (le_max_right ..).trans (isMaxOn_iff.mp hm q hq)⟩

/-- A single compact cylinder controls both speed and the operator norm
of the first derivative on the entire angular cover. -/
theorem bounds {σ : ℂ → ℝ} (hs : ContDiff ℝ ∞ σ) :
    ∃ B : ℝ≥0, ∀ p, ‖extended σ p‖ ≤ B ∧ ‖fderiv ℝ (extended σ) p‖ ≤ B :=
  bounds_of_constant_exterior (factor_smooth hs) (fun _ hz => (factor_flat hz).eq_of_nhds)

/-- The lifted geodesic field is globally bounded and globally Lipschitz for
the modified metric, and agrees with the given geodesic field before the
base leaves the open radius-two disk. -/
theorem bounded_lipschitz {σ : ℂ → ℝ} (hs : ContDiff ℝ ∞ σ) :
    ∃ B : ℝ≥0, LipschitzWith B (extended σ) ∧ ∀ p, ‖extended σ p‖ ≤ B := by
  obtain ⟨B,hB⟩ := bounds hs
  exact ⟨B, lipschitzWith_of_nnnorm_fderiv_le ((smooth hs).differentiable (by simp))
    (fun p => by exact_mod_cast (hB p).2), fun p => (hB p).1⟩

end TransportOkaGrauert.GeodesicFlowExtension
