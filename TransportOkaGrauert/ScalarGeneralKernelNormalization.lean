import TransportOkaGrauert.ScalarGeneralKernelRays

/-! # Probability-normalized angular normal operator -/

noncomputable section
namespace TransportOkaGrauert.ScalarGeneralKernel
open Complex Metric Set Filter MeasureTheory SimpleDiskTarget PathContinuation GeodesicFlowExtension
open JacobiEnlargement ScalarNormalLift
open scoped ContDiff Topology Interval

private def forward {σ : ℂ → ℝ} (F : Flow σ) (T : ℝ) (g : ℂ → ℂ) (a : ℂ) (θ : ℝ) :=
  ∫ t in (0:ℝ)..T, g (F.base (a,θ) t)

private theorem periodic_forward {σ : ℂ → ℝ} (F : Flow σ) (T : ℝ) (g : ℂ → ℂ) (a : ℂ) :
    Function.Periodic (forward F T g a) (2*Real.pi) := by
  intro θ
  apply intervalIntegral.integral_congr
  intro t _
  have e := congrArg Prod.fst (F.periodic (a,θ) (2*Real.pi) Circle.exp_two_pi t)
  exact congrArg g (by simpa [Flow.base] using e)

private theorem reversal_field (σ : ℂ → ℝ) (q : State) :
    chartVector σ (q+(0,Real.pi)) = -chartVector σ q := by
  simp [chartVector,Isothermal.angularDrift,Prod.smul_mk]
  ring

private theorem reverse_time {σ : ℂ → ℝ} (F : Flow σ) (a : ℂ) (θ t : ℝ) (ht : 0 ≤ t) :
    F.base (a,θ+Real.pi) t = F.base (a,θ) (-t) := by
  let p : State := (a,θ)
  let c : State := (0,Real.pi)
  let q (s : ℝ) := F.val (p,-s)+c
  have D (s : ℝ) : HasDerivAt q (chartVector F.factor (q s)) s := by
    have h := ((F.ode p (-s)).scomp s (hasDerivAt_id s).neg).add_const c
    simpa only [q,c,reversal_field,neg_one_smul] using h
  have smooth : ContDiff ℝ ∞ (chartVector F.factor) := contDiff_iff_contDiffAt.mpr fun x =>
    ChartRegularity.chartVector_contDiffAt x F.smoothFactor.contDiffAt
  have eq := ScalarGeneralUnrestricted.endpoint_unique smooth (a := 0) (b := t)
    (fun s _ => (F.ode (p+c) s).hasDerivWithinAt) (fun s _ => (D s).hasDerivWithinAt)
    (Or.inl (by simp [q,F.initial]))
  simpa [p,c,q,Flow.base] using congrArg Prod.fst (eq (right_mem_Icc.mpr ht))

private theorem supported_closed {g : ℂ → ℂ} (cg : Continuous g) (off : ∀ z, 1 < ‖z‖ → g z = 0) :
    ∀ z, 1 ≤ ‖z‖ → g z = 0 := by
  intro z hz
  rcases hz.lt_or_eq with h | h
  · exact off z h
  · have eq : (fun t : ℝ => g ((1+t) • z)) =ᶠ[𝓝[>] 0] fun _ => 0 := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      apply off
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by change 0 < 1+t; linarith [show 0 < t from ht]),← h,mul_one]
      linarith [show 0 < t from ht]
    have lim : Tendsto (fun t : ℝ => g ((1+t) • z)) (𝓝[>] 0) (𝓝 (g z)) := by
      have c : Continuous (fun t : ℝ => g ((1+t) • z)) := cg.comp ((continuous_const.add continuous_id).smul continuous_const)
      simpa using (c.continuousAt.tendsto (x := 0)).mono_left nhdsWithin_le_nhds
    exact tendsto_nhds_unique lim (tendsto_const_nhds.congr' eq.symm)

private theorem forward_eq_ray {σ : ℂ → ℝ} (simple : SimpleMetric σ) {a : ℂ} (ha : ‖a‖ < 1)
    (C : Coordinates σ a) (F : Flow σ) {T : ℝ} (hT : 0 < T) (esc : Escapes F T)
    (g : ℂ → ℂ) (cg : Continuous g) (off : ∀ z, 1 ≤ ‖z‖ → g z = 0) :
    C.rayAverage g = ∫ θ in (0:ℝ)..2*Real.pi, forward F T g a θ := by
  let h (p : ℝ × ℝ) := g (F.base (a,p.2) p.1)
  let A := Ioo (-Real.pi) Real.pi
  have haA : MeasurableSet A := measurableSet_Ioo
  have eq : C.rayAverage g = ∫ p in Ioi (0:ℝ) ×ˢ A, h p := by
    apply setIntegral_congr_fun (measurableSet_Ioi.prod haA)
    intro p hp
    exact ray_integrand simple ha C F g off p.2 p.1 hp.1
  have restrict : (∫ p in Ioc (0:ℝ) T ×ˢ A, h p) = ∫ p in Ioi (0:ℝ) ×ˢ A, h p := by
    symm
    apply setIntegral_eq_of_subset_of_forall_diff_eq_zero (measurableSet_Ioi.prod haA)
      (Set.prod_mono Ioc_subset_Ioi_self Subset.rfl)
    intro p hp
    have beyond : T < p.1 := not_le.mp (fun le => hp.2 ⟨⟨hp.1.1,le⟩, hp.1.2⟩)
    apply off
    by_contra! here
    have stays := F.stays (p := (a,p.2)) (R := 1) le_rfl ha.le here.le T ⟨hT.le,beyond.le⟩
    exact (not_lt_of_ge stays) (esc (a,p.2) ha.le).1
  have smooth : Continuous (fun p : ℝ × ℝ => h p.swap) :=
    cg.comp (continuous_fst.comp (F.smooth.continuous.comp ((continuous_const.prodMk continuous_fst).prodMk continuous_snd)))
  have integ : IntegrableOn (fun p : ℝ × ℝ => h p.swap) (A ×ˢ Ioc 0 T) (volume.prod volume) :=
    (smooth.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono Ioo_subset_Icc_self Ioc_subset_Icc_self)
  rw [eq,← restrict,Measure.volume_eq_prod ℝ ℝ,← setIntegral_prod_swap (μ := volume) (ν := volume) (Ioc 0 T) A h,
    setIntegral_prod _ integ]
  simp_rw [← intervalIntegral.integral_of_le hT.le (μ := volume)]
  change (∫ θ in Ioo (-Real.pi) Real.pi, forward F T g a θ) = _
  rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc,← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)]
  simpa only [show -Real.pi+2*Real.pi=Real.pi by ring,zero_add] using
    (periodic_forward F T g a).intervalIntegral_add_eq (-Real.pi) 0

/-- The real-valued positive-time identity. -/
theorem forward_eq_area_real {σ : ℂ → ℝ} (simple : SimpleMetric σ) {a : ℂ} (ha : ‖a‖ < 1)
    (C : Coordinates σ a) (F : Flow σ) {T : ℝ} (hT : 0 < T) (esc : Escapes F T)
    (g : ℂ → ℝ) (cg : Continuous g) (off : ∀ z, 1 ≤ ‖z‖ → g z = 0) :
    (∫ θ in (0:ℝ)..2*Real.pi, ∫ t in (0:ℝ)..T, g (F.base (a,θ) t)) =
      ∫ y in ball (0:ℂ) 1, C.density y * g y := by
  have e := (forward_eq_ray simple ha C F hT esc (fun y => (g y:ℂ)) (Complex.continuous_ofReal.comp cg)
    (fun z hz => by simp [off z hz])).symm.trans (C.rayAverage_eq_area _)
  unfold forward at e
  simp_rw [intervalIntegral.integral_of_le hT.le,intervalIntegral.integral_of_le Real.two_pi_pos.le,
    integral_complex_ofReal, Complex.real_smul,← Complex.ofReal_mul] at e
  rw [integral_complex_ofReal] at e
  apply Complex.ofReal_injective
  simpa only [intervalIntegral.integral_of_le hT.le,intervalIntegral.integral_of_le Real.two_pi_pos.le] using e

/-- The finite full-ray normal operator with normalized angular probability
is exactly the one-sided first-exit area kernel divided by π. -/
theorem normal_eq_area {σ : ℂ → ℝ} (simple : SimpleMetric σ) {a : ℂ} (ha : ‖a‖ < 1)
    (C : Coordinates σ a) (F : Flow σ) {T : ℝ} (hT : 0 < T) (esc : Escapes F T)
    (g : ℂ → ℂ) (sg : ContDiff ℝ ∞ g) (off : ∀ z, 1 < ‖z‖ → g z = 0) :
    normal F T g a = (Real.pi⁻¹ : ℝ) • ∫ y in ball (0:ℂ) 1, C.density y • g y := by
  have sf : ContDiff ℝ ∞ (forward F T g a) :=
    ScalarGeneralCauchy.integral_smooth (g := fun p : ℝ × ℝ => g (F.base (a,p.1) p.2))
      (sg.comp (contDiff_fst.comp (F.smooth.comp ((contDiff_const.prodMk contDiff_fst).prodMk contDiff_snd)))) hT
  have lineEq (θ : ℝ) : line F T g (a,θ) = forward F T g a (θ+Real.pi) + forward F T g a θ := by
    let f (s : ℝ) := g (F.base (a,θ) s)
    have cont : Continuous f := sg.continuous.comp (continuous_fst.comp (F.smooth.continuous.comp (continuous_const.prodMk continuous_id)))
    unfold line
    rw [← intervalIntegral.integral_add_adjacent_intervals (a := -T) (b := 0) (c := T)
      (f := f) (cont.intervalIntegrable _ _) (cont.intervalIntegrable _ _)]
    congr 1
    calc
      _ = ∫ s in (0:ℝ)..T, f (-s) := by rw [intervalIntegral.integral_comp_neg,neg_zero]
      _ = _ := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [uIcc_of_le hT.le] at hs
        exact congrArg g (reverse_time F a θ s hs.1).symm
  have equal : (∫ θ in (0:ℝ)..2*Real.pi, forward F T g a (θ+Real.pi)) =
      ∫ θ in (0:ℝ)..2*Real.pi, forward F T g a θ := by
    rw [intervalIntegral.integral_comp_add_right, zero_add,add_comm (2*Real.pi) Real.pi]
    simpa only [zero_add] using (periodic_forward F T g a).intervalIntegral_add_eq Real.pi 0
  rw [normal]
  simp_rw [lineEq]
  have tr : Continuous (fun θ => forward F T g a (θ+Real.pi)) := sf.continuous.comp (continuous_id.add continuous_const)
  rw [intervalIntegral.integral_add (tr.intervalIntegrable _ _)
    (sf.continuous.intervalIntegrable _ _),equal,← forward_eq_ray simple ha C F hT esc g sg.continuous (supported_closed sg.continuous off),
    ← C.rayAverage_eq_area]
  rw [← two_smul ℝ, smul_smul]
  congr 1
  field_simp

end TransportOkaGrauert.ScalarGeneralKernel
