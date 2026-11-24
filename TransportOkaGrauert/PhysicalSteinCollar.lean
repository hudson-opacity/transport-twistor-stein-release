import TransportOkaGrauert.PhysicalSteinZero

/-! # Positivity on the physical base collar

Pullback of the exterior derivative along the logarithmic polar parametrization
transfers the moving-frame estimate to every nonzero physical velocity.
The Cartesian computation supplies the missing zero section. -/

noncomputable section
namespace TransportOkaGrauert.PhysicalStein

open Complex ChartStein FrameLevi ConformalCollar CollarGluing Filter PolarCR Set Metric
open scoped ContDiff Topology

private abbrev Chart := ConformalFrame.Chart

theorem polar_norm (p : Chart) : ‖(polar p).2‖ = Real.exp p.2.2 := by
  have hu : ‖ConformalFrame.unit p.2.1‖ = 1 := by
    rw [← sq_eq_sq₀ (norm_nonneg _) zero_le_one, ← Complex.normSq_eq_norm_sq]
    simp [ConformalFrame.unit, Complex.normSq_apply, Complex.real_smul, -Complex.ofReal_cos, -Complex.ofReal_sin]
    nlinarith [Real.sin_sq_add_cos_sq p.2.1]
  simp [polar, hu]

theorem polar_smooth : ContDiff ℝ ∞ polar := by
  have hu : ContDiff ℝ ∞ ConformalFrame.unit :=
    (Real.contDiff_cos.smul contDiff_const).add (Real.contDiff_sin.smul contDiff_const)
  exact contDiff_fst.prodMk ((Real.contDiff_exp.comp (contDiff_snd.comp contDiff_snd)).smul
    (hu.comp (contDiff_fst.comp contDiff_snd)))

theorem polar_covers {p : E} (h : p.2 ≠ 0) :
    ∃ q : Chart, polar q = p ∧ q.2.2 = Real.log ‖p.2‖ := by
  refine ⟨(p.1, p.2.arg, Real.log ‖p.2‖), Prod.ext rfl ?_, rfl⟩
  change Real.exp (Real.log ‖p.2‖) • ConformalFrame.unit p.2.arg = p.2
  rw [Real.exp_log (norm_pos_iff.mpr h)]
  apply Complex.ext <;> simp [ConformalFrame.unit, Complex.real_smul,
    -Complex.ofReal_cos, -Complex.ofReal_sin, Complex.norm_mul_cos_arg, Complex.norm_mul_sin_arg]

theorem polar_submersion (p : Chart) : Function.Surjective (fderiv ℝ polar p) := by
  intro v
  have hn : (polar p).2 ≠ 0 := norm_ne_zero_iff.mp ((polar_norm p).trans_ne (Real.exp_ne_zero _))
  let a := v.2 / (polar p).2
  refine ⟨(v.1, a.im, a.re), ?_⟩
  rw [polar_derivative]
  refine Prod.ext ?_ ?_
  · rfl
  change (polar p).2 * ((a.re:ℂ) + I*a.im) = v.2
  rw [mul_comm I, Complex.re_add_im]
  dsimp [a]
  field_simp

theorem ddC_polar {σ : ℂ → ℝ} (hs : ContDiff ℝ ∞ σ) {p : Chart} (hr : p.2.2 < 0)
    {f : E → ℝ} (df : ContDiffAt ℝ 2 f (polar p)) (v w : Chart) :
    ddC (ConformalFrame.J σ) (f ∘ polar) p v w =
      ddC (J σ) f (polar p) (fderiv ℝ polar p v) (fderiv ℝ polar p w) := by
  have hv : ‖(polar p).2‖ < 1 := (polar_norm p).trans_lt (Real.exp_lt_one_iff.mpr hr)
  have dJ := (J_smooth hs hv).differentiableAt (by simp)
  have ddf := (df.fderiv_right (m := 1) (by decide)).differentiableAt one_ne_zero
  have dform : DifferentiableAt ℝ (dc (J σ) f) (polar p) :=
    (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℝ) (0 : Fin 1)).differentiableAt.comp
      (polar p) (ddf.clm_comp dJ).neg
  have eq : dc (ConformalFrame.J σ) (f ∘ polar) =ᶠ[𝓝 p]
      fun y => (dc (J σ) f (polar y)).compContinuousLinearMap (fderiv ℝ polar y) := by
    filter_upwards [(continuous_snd.comp continuous_snd).continuousAt.eventually_lt_const hr,
      polar_smooth.continuous.continuousAt.preimage_mem_nhds (df.eventually (by decide))] with y hy hfy
    change ContDiffAt ℝ 2 f (polar y) at hfy
    have d := fderiv_comp y (hfy.differentiableAt (by decide)) (polar_smooth.differentiable (by simp) y)
    apply ContinuousAlternatingMap.ext
    intro m
    change -(fderiv ℝ (f ∘ polar) y (ConformalFrame.J σ y (m 0))) =
      -(fderiv ℝ f (polar y) (J σ (polar y) (fderiv ℝ polar y (m 0))))
    rw [d, ContinuousLinearMap.comp_apply, polar_intertwines σ y hy]
  rw [ddC, eq.extDeriv_eq, extDeriv_pullback dform polar_smooth.contDiffAt (by simp; decide)]
  apply congrArg (extDeriv (dc (J σ) f) (polar p))
  funext i
  fin_cases i <;> rfl

/-- A strictly positive Levi pullback gives strict positivity on the physical
punctured disk, for the original `J` and physical real potential. -/
theorem strict_of_polar {σ : ℂ → ℝ} (hs : ContDiff ℝ ∞ σ) {p : Chart} (hr : p.2.2 < 0)
    {f : E → ℝ} (df : ContDiffAt ℝ 2 f (polar p))
    (h : StrictAt (ConformalFrame.J σ) (f ∘ polar) p) : StrictAt (J σ) f (polar p) := by
  intro v hv
  obtain ⟨w, rfl⟩ := polar_submersion p v
  have hn : w ≠ 0 := fun e => hv (by simp [e])
  simpa only [ddC_polar hs hr df, polar_intertwines σ p hr] using h w hn

theorem polar_barrier {p : Chart} (hp : p.2.2 < 0) :
    FrameLevi.radial (ConformalFrame.t p) = diskBarrier (polar p).2 := by
  let r := Real.exp (2*p.2.2)
  have h : r < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have h₁ : 0 < 1-r := sub_pos.mpr h
  have h₂ : 0 < 1+r := by dsimp [r]; positivity
  have eq : (Real.exp p.2.2)^2 = r := by rw [← Real.exp_nat_mul]; rfl
  simp only [FrameLevi.radial, ConformalFrame.t, ConformalFrame.radialParameter, diskBarrier, b₀,
    Complex.normSq_eq_norm_sq, polar_norm, eq]
  change Real.log (1+(1-r)/(1+r)) - Real.log ((1-r)/(1+r)) - Real.log 2 = -Real.log (1-r)
  rw [show 1+(1-r)/(1+r) = 2/(1+r) by field_simp; ring, Real.log_div (by norm_num) h₂.ne',
    Real.log_div h₁.ne' h₂.ne']
  ring

/-- A single physical base collar works for every velocity, including zero
and velocities arbitrarily close to the unit circle. -/
theorem positive_physical_base {σ : ℂ → ℝ} (simple : SimpleDiskTarget.SimpleMetric σ) :
    ∃ L > 0, ∃ N : Set ℂ, IsOpen N ∧ sphere (0 : ℂ) 1 ⊆ N ∧
    ∀ p ∈ domain, p.1 ∈ N →
      StrictAt (J σ) (fun y : E => diskBarrier y.2 - Real.log (defining L y.1)) p := by
  obtain ⟨L,hL,N,hN,hsphere,hstrict⟩ := positive_polar_base simple
  let M := N ∩ {z : ℂ | 0 < 1 - 2*L*b₀ z}
  have dc : Continuous b₀ := continuous_const.sub Complex.continuous_normSq
  have hM : IsOpen M := hN.inter (isOpen_lt continuous_const (continuous_const.sub (continuous_const.mul dc)))
  refine ⟨L,hL,M,hM,?_,?_⟩
  · intro z hz
    have norm : ‖z‖ = 1 := by simpa using hz
    exact ⟨hsphere hz, by simp [b₀, Complex.normSq_eq_norm_sq, norm]⟩
  intro p hp hm
  have hb₀ : 0 < b₀ p.1 := by
    rw [b₀, Complex.normSq_eq_norm_sq]
    nlinarith [hp.1, norm_nonneg p.1]
  have hgap := hm.2
  change 0 < 1-2*L*b₀ p.1 at hgap
  have hb : 0 < defining L p.1 := by
    rw [show defining L p.1 = b₀ p.1 * (1 - L*b₀ p.1) by unfold defining; ring]
    exact mul_pos hb₀ (by linarith)
  by_cases hv : p.2 = 0
  · obtain ⟨z,w⟩ := p
    change w = 0 at hv
    subst w
    exact strict_side_zero simple.smooth hL.le hb hgap
  obtain ⟨q, hq, ht⟩ := polar_covers hv
  have hr : q.2.2 < 0 := ht ▸ Real.log_neg (norm_pos_iff.mpr hv) hp.2
  have hq₁ : q.1 = p.1 := congrArg Prod.fst hq
  have df : ContDiffAt ℝ 2 (fun y : E => diskBarrier y.2 - Real.log (defining L y.1)) (polar q) := by
    rw [hq]
    exact (((diskBarrier_smooth hp.2).comp p contDiffAt_snd).sub
      ((((smooth_defining L).contDiffAt.log hb.ne').comp p contDiffAt_fst))).of_le (by decide)
  rw [← hq]
  apply strict_of_polar simple.smooth hr df
  have h := hstrict q (hq₁ ▸ hm.1) (hq₁ ▸ hp.1) hr
  apply StrictAt.congr h
  filter_upwards [(continuous_snd.comp continuous_snd).continuousAt.eventually_lt_const hr] with y hy
  simp only [FrameLevi.potential, ConformalFrame.frame, polar_barrier hy, Function.comp_apply, sub_eq_add_neg]
  rfl

/-- The numerical radius required by the physical collar-gluing theorem. -/
theorem exists_base_radius {σ : ℂ → ℝ} (simple : SimpleDiskTarget.SimpleMetric σ) :
    ∃ L > 0, ∃ rb < 1, ∀ p ∈ domain, rb < ‖p.1‖ →
      StrictAt (J σ) (fun y : E => diskBarrier y.2 - Real.log (defining L y.1)) p := by
  obtain ⟨L,hL,N,hN,hs,hp⟩ := positive_physical_base simple
  let K := closedBall (0 : ℂ) 1 \ N
  have hc : IsCompact K := (isCompact_closedBall (0 : ℂ) 1).diff hN
  by_cases he : K.Nonempty
  · obtain ⟨m,hm,hmax⟩ := hc.exists_isMaxOn he continuous_norm.continuousOn
    have hmle : ‖m‖ ≤ 1 := by simpa using hm.1
    have hmlt : ‖m‖ < 1 := lt_of_le_of_ne hmle (fun e => hm.2 (hs (by simpa using e)))
    refine ⟨L,hL,‖m‖,hmlt, fun p h hr => hp p h ?_⟩
    by_contra hn
    exact (not_le.mpr hr) (isMaxOn_iff.mp hmax p.1 ⟨by simpa using h.1.le, hn⟩)
  · refine ⟨L,hL,0,zero_lt_one,fun p h _ => hp p h ?_⟩
    by_contra hn
    exact he ⟨p.1, by simpa using h.1.le, hn⟩

/-- At a base point of negative curvature, the velocity logarithm already
has positive definite Levi form at every nonzero interior velocity. -/
theorem strict_velocity_of_negative {σ : ℂ → ℝ} (hs : ContDiff ℝ ∞ σ) {p : E}
    (hK : SimpleDiskTarget.curvature σ p.1 < 0) (hp : ‖p.2‖ < 1) (hv : p.2 ≠ 0) :
    StrictAt (J σ) (fun y : E => diskBarrier y.2) p := by
  obtain ⟨q, hq, ht⟩ := polar_covers hv
  have hr : q.2.2 < 0 := ht ▸ Real.log_neg (norm_pos_iff.mpr hv) hp
  have hq₁ : q.1 = p.1 := congrArg Prod.fst hq
  have df : ContDiffAt ℝ 2 (fun y : E => diskBarrier y.2) (polar q) := by
    rw [hq]
    exact ((diskBarrier_smooth hp).comp p contDiffAt_snd).of_le (by decide)
  rw [← hq]
  apply strict_of_polar hs hr df
  let t := ConformalFrame.t q
  have ht₀ : 0 < t := (ConformalFrame.equationsAt hs q hr).positive
  have ht₁ : t < 1 := by
    dsimp [t, ConformalFrame.t, ConformalFrame.radialParameter]
    apply (div_lt_one (by positivity)).mpr
    linarith [Real.exp_pos (2*q.2.2)]
  let F := ConformalFrame.frame σ
  let h := fun _ : Chart => (0:ℝ)
  have alongZero (P : Chart → Chart) : along P h = h := by
    funext x
    simp [along, h]
  have hB : 0 < LeviBoundary.vertical t (jet F h q) := by
    simp only [LeviBoundary.vertical, jet, alongZero]
    simpa [h] using
      div_pos (show 0 < 1-t^2 by nlinarith) (sq_pos_of_pos ht₀)
  have hS : 0 < LeviBoundary.schur t (jet F h q) := by
    have n := neg_pos.mpr (mul_neg_of_pos_of_neg (sub_pos.mpr ht₁) hK)
    simp only [LeviBoundary.schur, LeviBoundary.horizontal, LeviBoundary.mixedR,
      LeviBoundary.mixedJ, jet, alongZero]
    simpa [F, ConformalFrame.frame, LeviBoundary.schur, LeviBoundary.horizontal,
      LeviBoundary.mixedR, LeviBoundary.mixedJ, jet, along, h, hq₁] using n
  have pos : StrictAt (ConformalFrame.J σ) (potential F h) q := fun w hw =>
    ConformalFrame.positive_of_schur hs q hr (h := h) contDiffAt_const
      (by simp [h, along]) hB hS hw
  apply pos.congr
  filter_upwards [(continuous_snd.comp continuous_snd).continuousAt.eventually_lt_const hr] with y hy
  simp [potential,F,ConformalFrame.frame,h,polar_barrier hy]

/-- The complete smooth proper exhaustion, strictly plurisubharmonic outside
a compact subset, for every strictly negatively curved simple metric, including
nonconstant curvature. Only interior negativity is required. -/
theorem negative_curvature_exhaustion {σ : ℂ → ℝ} (simple : SimpleDiskTarget.SimpleMetric σ)
    (hK : ∀ z : ℂ, ‖z‖ < 1 → SimpleDiskTarget.curvature σ z < 0) :
    ∃ f : E → ℝ, (∀ p ∈ domain, ContDiffAt ℝ ∞ f p) ∧
      (∀ m : ℝ, IsCompact {p ∈ domain | f p ≤ m}) ∧
      ∃ K : Set E, IsCompact K ∧ K ⊆ domain ∧ ∀ p ∈ domain, p ∉ K → StrictAt (J σ) f p := by
  obtain ⟨L,hL,rb,hrb,hb⟩ := exists_base_radius simple
  obtain ⟨c,h⟩ := logarithmic_collar_exhaustion (J σ) (fun p : E => diskBarrier p.2) L 0 rb 0
    hL hrb zero_lt_one (fun p hp => (diskBarrier_smooth hp.2).comp p contDiffAt_snd)
    (by simp) (fun _ hp => (J_smooth simple.smooth hp.2).differentiableAt (by simp))
    (fun _ hp => J_sq σ hp.2)
    (fun p hp hr => strict_velocity_of_negative simple.smooth (hK _ hp.1) hp.2 (norm_pos_iff.mp hr)) hb
  exact ⟨_, h⟩

end TransportOkaGrauert.PhysicalStein
