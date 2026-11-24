import TransportOkaGrauert.ScalarGeneralKernel
import TransportOkaGrauert.ScalarNormalLift

/-! # Comparison of the first-exit and nonreturning geodesic flows -/

noncomputable section
namespace TransportOkaGrauert.ScalarGeneralKernel
open Metric Set Filter Complex MeasureTheory ConformalFrame SimpleRadialVariation
open JacobiEnlargement ScalarNormalLift SimpleDiskTarget PathContinuation GeodesicFlowExtension
open scoped ContDiff Topology Interval

private def shadow : Chart →L[ℝ] State := (ContinuousLinearMap.fst ℝ ℂ (ℝ × ℝ)).prod
  ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (.snd ℝ ℂ (ℝ × ℝ)))

private theorem shadow_field (σ : ℂ → ℝ) (q : Chart) : shadow (X σ q) = chartVector σ (shadow q) := by
  rw [(chart_columns σ q).1]; rfl

private theorem factor_field {σ : ℂ → ℝ} (F : Flow σ) (q : State) (hq : ‖q.1‖ ≤ 1) :
    chartVector F.factor q = chartVector σ q := by
  have e := F.germ hq
  simp [chartVector,Isothermal.angularDrift,e.self_of_nhds,e.fderiv_eq]

private theorem factor_smooth {σ : ℂ → ℝ} (F : Flow σ) : ContDiff ℝ ∞ (chartVector F.factor) :=
  contDiff_iff_contDiffAt.mpr fun p => ChartRegularity.chartVector_contDiffAt p F.smoothFactor.contDiffAt

private theorem shadow_ray {σ : ℂ → ℝ} {a : ℂ} (C : Coordinates σ a) (F : Flow σ) (θ T : ℝ)
    (inside : ∀ s ∈ Icc 0 T, ‖(C.flow (θ,s)).1‖ ≤ 1) :
    EqOn (fun s => shadow (C.flow (θ,s))) (fun s => F.val ((a,θ),s)) (Icc 0 T) := by
  apply ScalarGeneralUnrestricted.endpoint_unique (factor_smooth F) _ (fun t _ => (F.ode (a,θ) t).hasDerivWithinAt)
    (Or.inl (by rw [C.initial,F.initial]; rfl))
  intro t ht
  have h : fderiv ℝ C.flow (θ,t) (0,1) = X σ (C.flow (θ,t)) := (C.ode _ (inside t ht)).self_of_nhds
  have l : HasDerivAt (fun s => C.flow (θ,s)) (X σ (C.flow (θ,t))) t := by
    rw [← h]
    exact (C.flow_smooth.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_const t θ).prodMk (hasDerivAt_id t))
  have d := shadow.hasFDerivAt.comp_hasDerivAt t l
  rw [shadow_field,← factor_field F _ (inside t ht)] at d
  exact d.hasDerivWithinAt

private theorem flow_strict {σ : ℂ → ℝ} (simple : SimpleMetric σ) (F : Flow σ) {a : ℂ}
    (ha : ‖a‖ < 1) (θ : ℝ) {T : ℝ} (endpt : ‖F.base (a,θ) T‖ < 1) :
    ∀ t ∈ Icc 0 T, ‖F.base (a,θ) t‖ < 1 := by
  have closed := F.stays (p := (a,θ)) (R := 1) le_rfl ha.le endpt.le
  have geo : unitGeodesicOn σ (F.base (a,θ)) (F.angle (a,θ)) (Icc 0 T) := by
    intro t ht
    have eq := factor_field F (F.val ((a,θ),t)) (closed t ht)
    have D := (F.ode (a,θ) t).hasDerivWithinAt (s := Icc 0 T)
    rw [eq] at D
    exact ⟨(ContinuousLinearMap.fst ℝ ℂ ℝ).hasFDerivAt.comp_hasDerivWithinAt t D,
      (ContinuousLinearMap.snd ℝ ℂ ℝ).hasFDerivAt.comp_hasDerivWithinAt t D⟩
  intro t ht
  rcases ht.2.lt_or_eq with h | rfl
  · exact SimpleRadialStar.no_interior_contact simple geo (by simpa [Flow.base,F.initial] using ha)
      closed t ⟨ht.1,h⟩
  · exact endpt

private theorem first_return {σ : ℂ → ℝ} (simple : SimpleMetric σ) {a : ℂ} (ha : ‖a‖ < 1)
    (C : Coordinates σ a) (F : Flow σ) (θ : ℝ) {T : ℝ} (endpt : ‖F.base (a,θ) T‖ < 1) :
    ∀ s ∈ Icc 0 T, ‖(C.flow (θ,s)).1‖ ≤ 1 := by
  intro t ht
  by_contra! outside
  have sm : Continuous (fun s => (C.flow (θ,s)).1) :=
    continuous_fst.comp (C.flow_smooth.continuous.comp (continuous_const.prodMk continuous_id))
  obtain ⟨u,hu,bd,before⟩ := GeodesicEndpoint.first_exit ht.1 sm.continuousOn (by simpa [C.initial] using ha) outside.le
  have closed (s : ℝ) (hs : s ∈ Icc 0 u) : ‖(C.flow (θ,s)).1‖ ≤ 1 := by
    rcases hs.2.lt_or_eq with h | rfl
    · exact (before s ⟨hs.1,h⟩).le
    · exact bd.le
  have eq := congrArg Prod.fst (shadow_ray C F θ u closed (right_mem_Icc.mpr hu.1))
  change (C.flow (θ,u)).1 = F.base (a,θ) u at eq
  have strict := flow_strict simple F ha θ endpt u ⟨hu.1,hu.2.trans ht.2⟩
  rw [← eq,bd] at strict
  exact (lt_irrefl _ strict)

/-- The complete state, including its transported angle, agrees before exit. -/
theorem state_on_retained {σ : ℂ → ℝ} {a : ℂ} (C : Coordinates σ a) (F : Flow σ)
    (θ t : ℝ) (ht : 0 < t) (ret : t • (Circle.exp θ:ℂ) ∈ SimpleRadialStar.retained C.endpoint 1) :
    ((C.flow (θ,t)).1,(C.flow (θ,t)).2.1) = F.val ((a,θ),t) := by
  apply shadow_ray C F θ t _ (right_mem_Icc.mpr ht.le)
  intro s hs
  have h := ret (s/t) ⟨div_nonneg hs.1 ht.le,(div_le_one ht).mpr hs.2⟩
  rw [smul_smul,div_mul_cancel₀ _ ht.ne'] at h
  exact (C.polar θ s) ▸ h

theorem retained_of_inside {σ : ℂ → ℝ} (simple : SimpleMetric σ) {a : ℂ} (ha : ‖a‖ < 1)
    (C : Coordinates σ a) (F : Flow σ) (θ t : ℝ) (ht : 0 < t) (h : ‖F.base (a,θ) t‖ < 1) :
    t • (Circle.exp θ:ℂ) ∈ C.velocities := by
  have closed := first_return simple ha C F θ h
  have e := congrArg Prod.fst (shadow_ray C F θ t closed (right_mem_Icc.mpr ht.le))
  change (C.flow (θ,t)).1 = F.base (a,θ) t at e
  refine ⟨?_,?_⟩
  · intro s hs
    have b := closed (s*t) ⟨mul_nonneg hs.1 ht.le,mul_le_of_le_one_left ht.le hs.2⟩
    rw [smul_smul,← C.polar]; exact b
  · change C.endpoint (t • (Circle.exp θ:ℂ)) ∈ ball (0:ℂ) 1
    rw [← C.polar θ t,e]
    exact mem_ball_zero_iff.mpr h

/-- While time is positive the first-exit indicator agrees with evaluation
along the globally nonreturning flow for each source supported in the open disk. -/
theorem ray_integrand {σ : ℂ → ℝ} (simple : SimpleMetric σ) {a : ℂ} (ha : ‖a‖ < 1)
    (C : Coordinates σ a) (F : Flow σ) (g : ℂ → ℂ) (off : ∀ z, 1 ≤ ‖z‖ → g z = 0)
    (θ t : ℝ) (ht : 0 < t) :
    C.velocities.indicator (fun x => g (C.endpoint x)) (t • (Circle.exp θ : ℂ)) = g (F.base (a,θ) t) := by
  let v : ℂ := Circle.exp θ
  have from_retained (h : t • v ∈ C.velocities) : ∀ s ∈ Icc 0 t, ‖(C.flow (θ,s)).1‖ ≤ 1 := by
    intro s hs
    have r := h.1 (s/t) ⟨div_nonneg hs.1 ht.le,(div_le_one ht).mpr hs.2⟩
    rw [smul_smul,div_mul_cancel₀ _ ht.ne'] at r
    simpa only [C.polar] using r
  by_cases keep : t • v ∈ C.velocities
  · have e := congrArg Prod.fst (shadow_ray C F θ t (from_retained keep) (right_mem_Icc.mpr ht.le))
    change (C.flow (θ,t)).1 = F.base (a,θ) t at e
    rw [C.polar] at e
    exact (Set.indicator_of_mem keep _).trans (congrArg g e)
  · rw [Set.indicator_of_notMem keep]
    symm
    apply off
    by_contra! h
    have closed := first_return simple ha C F θ h
    have e := congrArg Prod.fst (shadow_ray C F θ t closed (right_mem_Icc.mpr ht.le))
    change (C.flow (θ,t)).1 = F.base (a,θ) t at e
    apply keep
    refine ⟨?_,?_⟩
    · intro s hs
      have b := closed (s*t) ⟨mul_nonneg hs.1 ht.le,mul_le_of_le_one_left ht.le hs.2⟩
      rw [smul_smul,← C.polar]; exact b
    · change C.endpoint (t • v) ∈ ball (0:ℂ) 1
      rw [← C.polar θ t,e]
      exact mem_ball_zero_iff.mpr h

end TransportOkaGrauert.ScalarGeneralKernel
