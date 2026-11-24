import TransportOkaGrauert.GeodesicEntrance
import TransportOkaGrauert.SimpleEnlargement
import TransportOkaGrauert.SmoothJacobiFamily
import TransportOkaGrauert.PolarCollar

/-! # A periodic strict Jacobi weight for every simple conformal disk

The entrance state is recorded by its complex unit direction. Arclength and
these physical entrance data descend through the angular covering, so the
weight constructed by smoothing frozen one-dimensional profiles is periodic.
-/

noncomputable section
namespace TransportOkaGrauert.PhysicalJacobiWeight

open Set Filter Metric Complex GeodesicFlowExtension SimpleDiskTarget PathContinuation
open JacobiEnlargement SimpleEnlargement
open scoped ContDiff Topology

def directions : Set State := closedBall (0:ℂ) 1 ×ˢ Icc (-Real.pi) Real.pi

theorem directions_compact : IsCompact directions := (isCompact_closedBall _ _).prod isCompact_Icc

theorem projected_X (σ : ℂ → ℝ) : PolarCollar.project (ConformalFrame.X σ) = chartVector σ := by
  funext p
  change PolarCollar.direction (ConformalFrame.X σ (p.1,p.2,0)) = _
  rw [(SimpleRadialVariation.chart_columns σ _).1]
  apply Prod.ext
  · rfl
  · rfl

private def physical (p : State) : ℂ × ℂ := (p.1,(Circle.exp p.2:ℂ))
private def anchor (g : ℂ × ℂ) : State := (g.1,g.2.arg)

private theorem physical_smooth : ContDiff ℝ ∞ physical := by
  have dv : ContDiff ℝ ∞ (fun t : ℝ => (Circle.exp t:ℂ)) := by
    simp only [Circle.coe_exp]
    exact (ofRealCLM.contDiff.mul contDiff_const).cexp
  exact contDiff_fst.prodMk (dv.comp contDiff_snd)

private theorem anchored {σ : ℂ → ℝ} (F : Flow σ) (p : State) (t : ℝ) :
    F.base (anchor (physical p)) t = F.base p t := by
  let a := (Circle.exp p.2 : ℂ).arg - p.2
  have ha : Circle.exp a = 1 := by
    simp only [a,sub_eq_add_neg,Circle.exp_add,Circle.exp_neg,Circle.exp_arg,mul_inv_cancel]
  have ep : anchor (physical p) = p+(0,a) := by ext <;> simp [anchor,physical,a]
  simpa only [ep,Flow.base,Prod.fst_add,add_zero] using congrArg Prod.fst (F.periodic p a ha t)

/-- Smooth in ambient directions along the closed disk, with the positive
Riccati defect evaluated along the actual lifted geodesic field. -/
theorem exists_periodic_weight {σ : ℂ → ℝ} (simple : SimpleMetric σ) :
    ∃ h : State → ℝ, (∀ (z : ℂ) (a b : ℝ), Circle.exp a = Circle.exp b → h (z,a) = h (z,b)) ∧
      ∀ p ∈ directions, ContDiffAt ℝ ∞ h p ∧
        0 < fderiv ℝ (fun q => fderiv ℝ h q (chartVector σ q)) p (chartVector σ p) -
          curvature σ p.1 - (fderiv ℝ h p (chartVector σ p))^2 := by
  obtain ⟨F⟩ := JacobiEnlargement.exists_flow simple
  obtain ⟨B,hB,sB⟩ := simple_radius F simple
  obtain ⟨T,hT,A,hA,_,out⟩ := F.uniform_escape simple
  let R := min A B
  have hR : 1 < R := lt_min hA hB
  have bp : 0 < B := zero_lt_one.trans hB
  have esc (p : State) (hp : ‖p.1‖ ≤ R) : R < ‖F.base p T‖ :=
    (min_le_left ..).trans_lt (out p (hp.trans (min_le_left ..)))
  let ell := fun p => -F.entranceTime R p
  let hit := fun p => F.val (p,F.entranceTime R p)
  let entry := physical ∘ hit
  let z := fun g t => B⁻¹ • F.base (anchor g) t
  let θ := fun g t => F.angle (anchor g) t
  let φ := fun p s => F.val (p,s)
  have hr (p : State) (hp : p ∈ directions) : ‖p.1‖ < R :=
    (mem_closedBall_zero_iff.mp hp.1).trans_lt hR
  have eh (p : State) (hp : p ∈ directions) := F.entrance_smooth hR.le hT esc (hr p hp)
  have hzero (p : State) : F.base (hit p) (ell p) = p.1 := by simp [hit,ell,Flow.base,F.group,F.initial]
  have kend (p : State) (hp : p ∈ directions) :
      curvature (rescale F.factor B) (z (entry p) (ell p)) = curvature σ p.1 := by
    change curvature (rescale F.factor B) (B⁻¹ • F.base (anchor (physical (hit p))) (ell p)) = _
    rw [rescale_curvature F.smoothFactor bp,smul_smul,mul_inv_cancel₀ bp.ne',one_smul,anchored,hzero]
    exact F.curvature_germ (mem_closedBall_zero_iff.mp hp.1)
  have shifted (p : State) {a : ℝ} (ha : Circle.exp a = 1) :
      entry (p+(0,a)) = entry p ∧ ell (p+(0,a)) = ell p := by
    simp [entry,physical,hit,ell,F.entrance_shift R p ha,F.periodic p a ha,Circle.exp_add,ha]
  have ode (p : State) (hp : p ∈ directions) :
      ∀ᶠ s in 𝓝 0, HasDerivAt (φ p) (chartVector σ (φ p s)) s := by
    have eq := F.germ (mem_closedBall_zero_iff.mp hp.1)
    have ev : Tendsto (F.base p) (𝓝 0) (𝓝 p.1) := by
      simpa [Flow.base,F.initial] using (continuous_fst.comp
        (F.smooth.continuous.comp (continuous_const.prodMk continuous_id))).continuousAt (x := (0:ℝ)) |>.tendsto
    filter_upwards [ev.eventually eq.eventuallyEq_nhds] with t ht
    simpa only [φ,chartVector,Isothermal.angularDrift,ht.eq_of_nhds,ht.fderiv_eq] using F.ode p t
  obtain ⟨h,inv,good⟩ := SmoothJacobiFamily.exists_invariant_angular_weight directions_compact
    sB hT.le entry ell (chartVector σ) φ z θ
    (fun p hp => physical_smooth.contDiffAt.comp p (F.smooth.contDiffAt.comp p (contDiffAt_id.prodMk (eh p hp))))
    (fun p hp => (eh p hp).neg)
    (fun p hp => F.entrance_bounded hR.le hT esc (hr p hp))
    (((ChartJacobi.curvature_contDiff simple.smooth).continuous.comp continuous_fst).continuousOn.congr kend)
    (fun p _ => ((contDiff_const (c := B⁻¹)).smul (contDiff_fst.comp (F.smooth.comp ((contDiff_const (c := anchor (entry p))).prodMk contDiff_id)))).contDiffOn)
    (fun p _ => unscale_ray F.smoothFactor bp (F.geo (anchor (entry p)) _))
    (fun p hp t ht => by
      have ed := (F.entrance_spec hR.le hT esc (hr p hp)).2
      have bnd := F.stays (p := hit p) hR.le ed.le (by rw [hzero]; exact (hr p hp).le) t ht
      rw [mem_closedBall_zero_iff]
      change ‖B⁻¹ • F.base (anchor (physical (hit p))) t‖ ≤ 1
      rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr bp.le),anchored,inv_mul_le_iff₀ bp,mul_one]
      exact bnd.trans (min_le_right ..))
    (fun p _ => (ChartRegularity.chartVector_contDiffAt p simple.smooth.contDiffAt).differentiableAt (by simp))
    (fun p _ => F.initial p)
    (fun p hp => by
      filter_upwards [ode p hp,F.entrance_advance hR.le hT esc (hr p hp)] with s ds hs
      refine ⟨ds,congrArg physical hs.2,?_⟩
      change -F.entranceTime R (F.val (p,s)) = -F.entranceTime R p + s
      rw [hs.1]; ring)
  refine ⟨h,?_,fun p hp => by simpa only [kend p hp] using good p hp⟩
  intro z a b e
  have per : Circle.exp (a-b) = 1 := by simp [sub_eq_add_neg,Circle.exp_add,Circle.exp_neg,e]
  obtain ⟨e₁,e₂⟩ := shifted (z,b) per
  simpa using inv _ _ e₁ e₂

/-- The same weight and strict inequality on the entire real angular cover. -/
theorem exists_global_weight {σ : ℂ → ℝ} (simple : SimpleMetric σ) :
    ∃ h : State → ℝ, (∀ (z : ℂ) (a b : ℝ), Circle.exp a = Circle.exp b → h (z,a) = h (z,b)) ∧
      ∀ p : State, ‖p.1‖ ≤ 1 → ContDiffAt ℝ ∞ h p ∧
        0 < FrameLevi.along (chartVector σ) (FrameLevi.along (chartVector σ) h) p -
          curvature σ p.1 - (FrameLevi.along (chartVector σ) h p)^2 := by
  obtain ⟨h,per,g⟩ := exists_periodic_weight simple
  refine ⟨h,per,?_⟩
  intro p hp
  let a := (Circle.exp p.2 : ℂ).arg - p.2
  let v : State := (0,a)
  have ev : Circle.exp a = 1 := by
    simp only [a,sub_eq_add_neg,Circle.exp_add,Circle.exp_neg,Circle.exp_arg,mul_inv_cancel]
  have angle : (p+v).2 = (Circle.exp p.2 : ℂ).arg := by simp [v,a]
  have mem : p+v ∈ directions := ⟨by simpa [v] using hp,angle ▸ ⟨(neg_pi_lt_arg _).le,arg_le_pi _⟩⟩
  have trans : (fun y => h (y+v)) = h := by
    funext y
    change h (y.1+0,y.2+a) = h (y.1,y.2)
    rw [add_zero]
    apply per y.1 (y.2+a) y.2
    simp [Circle.exp_add,ev]
  have X (y : State) : chartVector σ (y+v) = chartVector σ y := by
    simp [v,chartVector,Circle.exp_add,ev]
  have d (y : State) : fderiv ℝ h (y+v) = fderiv ℝ h y := by rw [← fderiv_comp_add_right,trans]
  let Xh := FrameLevi.along (chartVector σ) h
  have tr₁ : (fun y => Xh (y+v)) = Xh := by funext y; simp [Xh,FrameLevi.along,d,X]
  have d₁ (y : State) : fderiv ℝ Xh (y+v) = fderiv ℝ Xh y := by rw [← fderiv_comp_add_right,tr₁]
  obtain ⟨sm,pos⟩ := g (p+v) mem
  have sh := sm.comp p (contDiffAt_id.add (contDiffAt_const (c := v)))
  change ContDiffAt ℝ ∞ (fun y => h (y+v)) p at sh
  rw [trans] at sh
  change 0 < fderiv ℝ Xh (p+v) (chartVector σ (p+v)) - curvature σ (p+v).1 -
    (fderiv ℝ h (p+v) (chartVector σ (p+v)))^2 at pos
  rw [d₁,X,d] at pos
  exact ⟨sh,by simpa [v,FrameLevi.along,Xh] using pos⟩

end TransportOkaGrauert.PhysicalJacobiWeight
