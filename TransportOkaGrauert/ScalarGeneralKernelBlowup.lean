import TransportOkaGrauert.ScalarGeneralKernelJoint

/-! # The joint radial extension of the ray kernel on compact subdisks -/

noncomputable section
namespace TransportOkaGrauert.ScalarGeneralKernel
open Complex Metric Set Filter MeasureTheory
open scoped ContDiff Topology Manifold

private abbrev Parameter := (ℂ × ℝ) × ℂ

private theorem extend_product {U K : Set (ℂ × ℂ)} (op : IsOpen U) (closed : IsClosed K) (inside : K ⊆ U)
    {L : ℂ × ℂ → ℂ} (sL : ContDiffOn ℝ ∞ L U) :
    ∃ W : ℂ × ℂ → ℂ, ContDiff ℝ ∞ W ∧ ∀ q ∈ K, W =ᶠ[𝓝 q] L := by
  obtain ⟨χ,zero,one,_⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed (𝓘(ℝ,ℂ × ℂ)) (n := ⊤)
    op.isClosed_compl closed (Set.disjoint_left.mpr (fun _ hU hK => hU (inside hK)))
  have sχ := contMDiff_iff_contDiff.mp χ.contMDiff
  have h₀ := mem_nhdsSet_iff_forall.mp zero
  have h₁ := mem_nhdsSet_iff_forall.mp one
  refine ⟨fun q => χ q • L q,contDiff_iff_contDiffAt.mpr (fun q => ?_),fun q hq => ?_⟩
  · by_cases hq : q ∈ U
    · exact sχ.contDiffAt.smul (sL.contDiffAt (op.mem_nhds hq))
    · apply (contDiffAt_const (c := (0:ℂ))).congr_of_eventuallyEq
      filter_upwards [h₀ q hq] with y hy
      simp [hy]
  · filter_upwards [h₁ q hq] with y hy
    simp [hy]

private def endpointOf (p : Parameter) := (p.1.1,p.1.1+p.1.2 • p.2)
private def centreOf (p : Parameter) := (p.1.1,p.1.1)
private def S (W : ℂ × ℂ → ℂ) (p : Parameter) :=
  ∫ t in (0:ℝ)..1, verticalDerivative W (p.1.1,p.1.1+t • (p.1.2 • p.2)) p.2

private theorem endpoint_smooth : ContDiff ℝ ∞ endpointOf :=
  (contDiff_fst.comp contDiff_fst).prodMk
    ((contDiff_fst.comp contDiff_fst).add ((contDiff_snd.comp contDiff_fst).smul contDiff_snd))

private theorem S_smooth {W : ℂ × ℂ → ℂ} (h : ContDiff ℝ ∞ W) : ContDiff ℝ ∞ (S W) := by
  let point (u : Parameter × ℝ) := (u.1.1.1,u.1.1.1+u.2 • (u.1.1.2 • u.1.2))
  have a : ContDiff ℝ ∞ (fun u : Parameter × ℝ => u.1.1.1) := contDiff_fst.comp (contDiff_fst.comp contDiff_fst)
  have r : ContDiff ℝ ∞ (fun u : Parameter × ℝ => u.1.1.2) := contDiff_snd.comp (contDiff_fst.comp contDiff_fst)
  have v : ContDiff ℝ ∞ (fun u : Parameter × ℝ => u.1.2) := contDiff_snd.comp contDiff_fst
  have sp : ContDiff ℝ ∞ point := a.prodMk (a.add (contDiff_snd.smul (r.smul v)))
  have V : ContDiff ℝ ∞ (verticalDerivative W) := (h.fderiv_right (m := ∞) (by simp)).clm_comp contDiff_const
  exact ScalarGeneralCauchy.integral_smooth (g := fun u : Parameter × ℝ => verticalDerivative W (point u) u.1.2)
    ((V.comp sp).clm_apply v) one_pos

private theorem S_eq {W : ℂ × ℂ → ℂ} (h : ContDiff ℝ ∞ W) (a : ℂ) (r : ℝ) (v : ℂ) :
    S W ((a,r),v) = slope (fun y => W (a,y)) a (r,v) := by
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  rw [verticalDerivative_eq (h.differentiable (by simp) _)]

private theorem regular_norm {m : ℝ} (hm : 0 < m) :
    ∃ N : ℂ → ℝ, ContDiff ℝ ∞ N ∧ (∀ v, 0 < N v) ∧ ∀ v, m/2 ≤ ‖v‖ → N v = ‖v‖ := by
  let χ : ContDiffBump (0:ℂ) := ⟨m/4,m/2,by positivity,by linarith⟩
  let N (v : ℂ) := Real.sqrt (Complex.normSq v + χ v)
  have pos (v : ℂ) : 0 < Complex.normSq v + χ v := by
    by_cases h : v = 0
    · subst v
      rw [χ.one_of_mem_closedBall (mem_closedBall_self χ.rIn_pos.le)]
      simp
    · have hn : 0 < Complex.normSq v := by rw [Complex.normSq_eq_norm_sq]; positivity
      exact add_pos_of_pos_of_nonneg hn χ.nonneg
  have smooth : ContDiff ℝ ∞ Complex.normSq := by
    have eq : (fun z : ℂ => Complex.normSq z) = fun z : ℂ => z.re*z.re+z.im*z.im := by funext z; rfl
    change ContDiff ℝ ∞ (fun z : ℂ => Complex.normSq z)
    rw [eq]
    exact (reCLM.contDiff.mul reCLM.contDiff).add (imCLM.contDiff.mul imCLM.contDiff)
  refine ⟨N,(smooth.add χ.contDiff).sqrt (fun v => (pos v).ne'),fun v => Real.sqrt_pos.mpr (pos v),?_⟩
  intro v hv
  have zero : χ v = 0 := χ.zero_of_le_dist (by simpa [χ] using hv)
  simp [N,zero,Complex.normSq_eq_norm_sq]

/-- On every compact part of the disk a single radial amplitude works
simultaneously for all centres and directions. All mixed centre, radius and
direction derivatives exist on the polar face. -/
theorem compact_radial_amplitude {σ : ℂ → ℝ} (simple : SimpleDiskTarget.SimpleMetric σ)
    {K : Set ℂ} (closed : IsClosed K) (inside : K ⊆ ball (0:ℂ) 1) :
    ∃ L : ℂ × ℂ → ℂ, ∃ A : (ℂ × ℝ) × ℂ → ℝ,
      ContDiff ℝ ∞ A ∧ (∀ a ∈ ball (0:ℂ) 1, ∃ C : Coordinates σ a, ∀ y ∈ ball (0:ℂ) 1, C.density y = jointDensity L (a,y)) ∧
      ∀ a ∈ K, ∀ v : ℂ, ‖v‖ = 1 → ContDiffAt ℝ ∞ A ((a,0),v) ∧
        A ((a,0),v) = Real.exp (σ a) ∧
        ∀ᶠ p : (ℂ × ℝ) × ℂ in 𝓝 ((a,0),v), 0 < p.1.2 →
          p.1.2 * jointDensity L (p.1.1,p.1.1+p.1.2 • p.2) = A p := by
  let B := ball (0:ℂ) 1
  obtain ⟨_,L,_,sL,_,fam⟩ := exists_joint_kernel simple
  obtain ⟨W,sW,agree⟩ := extend_product (isOpen_ball.prod isOpen_ball) (closed.prod closed)
    (prod_mono inside inside) sL
  let D (p : Parameter) := (verticalDerivative W (endpointOf p)).det
  have compact : IsCompact K := (isCompact_closedBall (0:ℂ) 1).of_isClosed_subset closed (inside.trans ball_subset_closedBall)
  obtain ⟨m,hm,lb⟩ := compact.exists_forall_le' (Real.continuous_exp.comp simple.smooth.continuous).continuousOn
    (a := 0) (fun _ _ => Real.exp_pos _)
  obtain ⟨N,sN,posN,normN⟩ := regular_norm hm
  let A (p : Parameter) := D p / N (S W p)
  have d (p : Parameter) : ContDiffAt ℝ ∞ D p := by
    simp_rw [D,determinant_formula]
    have V : ContDiff ℝ ∞ (verticalDerivative W) := (sW.fderiv_right (m := ∞) (by simp)).clm_comp contDiff_const
    have M (v : ℂ) := (V.comp endpoint_smooth).clm_apply (contDiff_const (c := v))
    exact (((reCLM.contDiff.comp (M 1)).mul (imCLM.contDiff.comp (M I))).sub
      ((reCLM.contDiff.comp (M I)).mul (imCLM.contDiff.comp (M 1)))).contDiffAt
  have sA : ContDiff ℝ ∞ A := (contDiff_iff_contDiffAt.mpr d).div (sN.comp (S_smooth sW)) (fun _ => (posN _).ne')
  refine ⟨L,A,sA,fun a ha => ?_,fun a ha v hv => ?_⟩
  · obtain ⟨C,_,_,h⟩ := fam a ha
    exact ⟨C,h⟩
  · let c := Real.exp (σ a)
    have hc : 0 < c := Real.exp_pos _
    have inB := inside ha
    have germ := agree (a,a) ⟨ha,ha⟩
    have grad := germ.fderiv (𝕜 := ℝ)
    have slice (b : ℂ) (hb : b ∈ B) : L (b,b) = 0 := by
      obtain ⟨C,_,t,_⟩ := fam b hb
      exact (congrFun t b).symm.trans (C.log_zero (mem_ball_zero_iff.mp hb))
    have diffL := ((sL (a,a) ⟨inB,inB⟩).contDiffAt
      ((isOpen_ball.prod isOpen_ball).mem_nhds ⟨inB,inB⟩)).differentiableAt (by simp)
    obtain ⟨C,_,t,_⟩ := fam a inB
    have M : verticalDerivative W (a,a) = c • ContinuousLinearMap.id ℝ ℂ := by
      rw [show verticalDerivative W (a,a) = verticalDerivative L (a,a) by
        unfold verticalDerivative; rw [grad.self_of_nhds],verticalDerivative_eq diffL,← t]
      exact C.log_derivative (mem_ball_zero_iff.mp inB)
    have D0 : D ((a,0),v) = c ^ 2 := by
      simp only [D,endpointOf,zero_smul,add_zero,M]
      change LinearMap.det (c • (LinearMap.id : ℂ →ₗ[ℝ] ℂ)) = _
      rw [LinearMap.det_smul, Complex.finrank_real_complex, LinearMap.det_id, mul_one]
    have N0 : ‖S W ((a,0),v)‖ = c := by
      rw [S_eq sW,slope_origin,← verticalDerivative_eq (sW.differentiable (by simp) _),M]
      change ‖c • v‖ = c
      rw [norm_smul, Real.norm_eq_abs,abs_of_pos hc,hv,mul_one]
    have low : m/2 < c := by have := lb a ha; change m ≤ c at this; linarith
    have norm0 : N (S W ((a,0),v)) = c := (normN _ (N0 ▸ low.le)).trans N0
    refine ⟨sA.contDiffAt,?_,?_⟩
    · change D ((a,0),v) / N (S W ((a,0),v)) = c
      rw [D0,norm0]; field_simp
    · have tend : Tendsto endpointOf (𝓝 ((a,0),v)) (𝓝 (a,a)) := by
        simpa [endpointOf] using endpoint_smooth.continuous.tendsto ((a,0),v)
      have center : Tendsto centreOf (𝓝 ((a,0),v)) (𝓝 (a,a)) :=
        ((continuous_fst.comp continuous_fst).prodMk (continuous_fst.comp continuous_fst)).tendsto _
      have hb : ∀ᶠ p : Parameter in 𝓝 ((a,0),v), p.1.1 ∈ B :=
        (continuous_fst.comp continuous_fst).continuousAt.eventually (isOpen_ball.mem_nhds inB)
      have Dpos : ∀ᶠ p in 𝓝 ((a,0),v), 0 < D p := (d _).continuousAt.eventually (Ioi_mem_nhds (D0 ▸ sq_pos_of_pos hc))
      have Snorm : ∀ᶠ p in 𝓝 ((a,0),v), m/2 < ‖S W p‖ :=
        (S_smooth sW).continuous.norm.continuousAt.eventually (Ioi_mem_nhds (show m/2 < ‖S W ((a,0),v)‖ by rwa [N0]))
      filter_upwards [tend.eventually germ,tend.eventually grad,center.eventually germ,hb,Dpos,Snorm]
        with p eq diff eq0 hB dp np
      intro hr
      have ep := slope_eq (W := fun y => W (p.1.1,y)) (sW.comp (contDiff_const.prodMk contDiff_id)) p.1.1 p.1.2 p.2
      rw [← S_eq sW] at ep
      change _ = W (endpointOf p) - W (centreOf p) at ep
      rw [eq,eq0,show L (centreOf p) = 0 from slice _ hB,sub_zero] at ep
      change p.1.2 * (|(verticalDerivative L (endpointOf p)).det| / ‖L (endpointOf p)‖) =
        (verticalDerivative W (endpointOf p)).det / N (S W p)
      rw [← show verticalDerivative W (endpointOf p) = verticalDerivative L (endpointOf p) by
        unfold verticalDerivative; rw [diff],← ep,norm_smul,Real.norm_eq_abs,abs_of_pos hr,
        abs_of_pos dp,normN _ np.le]
      field_simp
      rfl

end TransportOkaGrauert.ScalarGeneralKernel
