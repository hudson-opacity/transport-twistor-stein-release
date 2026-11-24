import TransportOkaGrauert.ScalarGeneralWAngular

/-! # From the angular kernel to its action on an arbitrary smooth test function -/

noncomputable section
namespace TransportOkaGrauert.ScalarGeneralKernel
open Complex Metric Set Filter MeasureTheory SimpleDiskTarget SimpleRadialVariation ConformalFrame
open JacobiEnlargement GeodesicFlowExtension ScalarNormalLift
open scoped ContDiff Topology Interval

def perpendicularSource (σ : ℂ → ℝ) (g : ℂ → ℝ) (p : State) :=
  Real.exp (-σ p.1) * fderiv ℝ g p.1 (I*(Circle.exp p.2:ℂ))

theorem smooth_source {σ : ℂ → ℝ} (sσ : ContDiff ℝ ∞ σ) {g : ℂ → ℝ} (sg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (perpendicularSource σ g) := by
  have rot : ContDiff ℝ ∞ (fun t : ℝ => (Circle.exp t:ℂ)) := (ofRealCLM.contDiff.mul contDiff_const).cexp
  exact ((sσ.comp contDiff_fst).neg.exp).mul (((sg.fderiv_right (m := ∞) (by simp)).comp contDiff_fst).clm_apply
    (contDiff_const.mul (rot.comp contDiff_snd)))

private theorem test_germ {B : Set ℂ} (hB : IsClosed B) {g : ℂ → ℝ} (off : ∀ z ∉ B, g z = 0)
    {z : ℂ} (hz : z ∉ B) : g =ᶠ[𝓝 z] fun _ => 0 :=
  Filter.eventually_of_mem (hB.isOpen_compl.mem_nhds hz) (fun p hp => off p hp)

def spatialWeight {σ : ℂ → ℝ} {a : ℂ} (C : Coordinates σ a) (E : ℂ × ℂ → ℂ)
    (W : ℂ × ℂ → ℝ) (g : ℂ → ℝ) (y : ℂ) :=
  ‖C.logMap y‖ * alpha σ E (a,C.logMap y) * W (a,y) * g y

theorem weight_continuous {σ : ℂ → ℝ} (simple : SimpleMetric σ) {a : ℂ} (C : Coordinates σ a)
    {E : ℂ × ℂ → ℂ} (sE : ContDiff ℝ ∞ E) {W : ℂ × ℂ → ℝ} (sW : ContDiff ℝ ∞ W)
    {B : Set ℂ} (hB : IsClosed B) (inside : B ⊆ ball (0:ℂ) 1) {g : ℂ → ℝ} (sg : ContDiff ℝ ∞ g)
    (off : ∀ z ∉ B, g z = 0) : Continuous (spatialWeight C E W g) := by
  apply continuous_iff_continuousAt.mpr
  intro y
  by_cases hy : y ∈ ball (0:ℂ) 1
  · have h := ((C.log_smooth y hy).contDiffAt (isOpen_ball.mem_nhds hy)).continuousAt
    exact (((h.norm.mul ((alpha_smooth simple.smooth sE).continuous.continuousAt.comp (continuousAt_const.prodMk h))).mul
      (sW.continuous.continuousAt.comp (continuousAt_const.prodMk continuousAt_id))).mul sg.continuous.continuousAt)
  · apply (continuousAt_const (y := (0:ℝ))).congr_of_eventuallyEq
    filter_upwards [test_germ hB off (fun b => hy (inside b))] with z hz
    simp [spatialWeight,hz]

theorem angular_test {σ : ℂ → ℝ} (simple : SimpleMetric σ) {a : ℂ} (ha : ‖a‖ < 1)
    (C : Coordinates σ a) {E : ℂ × ℂ → ℂ} (sE : ContDiff ℝ ∞ E) (ce : C.endpoint = fun v => E (a,v)) (F : Flow σ)
    {B : Set ℂ} (hB : IsCompact B) (inside : B ⊆ ball (0:ℂ) 1) {W : ℂ × ℂ → ℝ}
    (formula : ∀ y ∈ B, a ≠ y → let x := C.logMap y
      W (a,y) = fderiv ℝ (alpha σ E) (a,x) (0,I*x) / (‖x‖^2*(alpha σ E (a,x))^3))
    (g : ℂ → ℝ) (sg : ContDiff ℝ ∞ g) (off : ∀ z ∉ B, g z = 0) :
    ∃ b h : ℂ → ℝ, ContDiff ℝ ∞ b ∧ ContDiff ℝ ∞ h ∧ ∀ θ r : ℝ, 0 < r →
      let x := turn r θ
      let p := F.val ((a,θ),r)
      r * perpendicularSource σ g p = b x*angularD h x ∧
      r * spatialWeight C E W g p.1 = -(angularD b x)*h x := by
  let Q := C.logMap '' B
  have Qcompact : IsCompact Q := hB.image_of_continuousOn (C.log_smooth.continuousOn.mono inside)
  have vopen : IsOpen C.velocities := by rw [C.velocities_eq_beforeExit simple ha]; exact SimpleRadialStar.isOpen_beforeExit C.endpoint_smooth.continuous 1
  have sub : Q ⊆ C.velocities := by
    rintro _ ⟨y,hy,rfl⟩
    have ey := (C.right y (inside hy)).2
    exact ⟨(C.right y (inside hy)).1,show C.endpoint (C.logMap y) ∈ ball (0:ℂ) 1 by rw [ey]; exact inside hy⟩
  obtain ⟨χ,sχ,one,zero⟩ := SimpleRadialDivision.cutoff vopen Qcompact.isClosed sub
  let A (x : ℂ) := alpha σ E (a,x)
  have sA : ContDiff ℝ ∞ A := (alpha_smooth simple.smooth sE).comp (contDiff_const.prodMk contDiff_id)
  let b (x : ℂ) := χ x / A x
  let h (x : ℂ) := χ x * g (C.endpoint x)
  have sb : ContDiff ℝ ∞ b := contDiff_iff_contDiffAt.mpr fun x => by
    by_cases hx : x ∈ C.velocities
    · exact sχ.contDiffAt.div sA.contDiffAt (alpha_on_velocities simple sE ha C ce hx).ne'
    · apply (contDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq
      filter_upwards [zero x hx] with v hv
      simp [b,hv]
  have sh : ContDiff ℝ ∞ h := sχ.mul (sg.comp C.endpoint_smooth)
  refine ⟨b,h,sb,sh,fun θ r hr => ?_⟩
  intro x p
  have nr : ‖x‖ = r := by simp [x,turn,hr.le]
  have nx : x ≠ 0 := norm_ne_zero_iff.mp (nr ▸ hr.ne')
  have endpoint (keep : x ∈ C.velocities) : C.endpoint x = p.1 := by
    have e := congrArg Prod.fst (state_on_retained C F θ r hr keep.1)
    change (C.flow (θ,r)).1 = p.1 at e
    exact (C.polar θ r).symm.trans e
  by_cases data : p.1 ∈ B
  · have keep := retained_of_inside simple ha C F θ r hr (mem_ball_zero_iff.mp (inside data))
    have ey := endpoint keep
    have logEq : C.logMap p.1 = x := by rw [← ey]; exact C.left x keep.1 keep.2
    have xQ : x ∈ Q := ⟨p.1,data,logEq⟩
    have hx : χ x = 1 := (one x xQ).self_of_nhds
    have pos : 0 < A x := alpha_on_velocities simple sE ha C ce keep
    have germH : h =ᶠ[𝓝 x] g ∘ C.endpoint := by filter_upwards [one x xQ] with v hv; simp [h,hv]
    have hd := (sg.differentiable (by simp) _).hasFDerivAt.comp x (C.endpoint_smooth.differentiable (by simp) x).hasFDerivAt
    have hH := germH.fderiv_eq (𝕜 := ℝ) |>.trans hd.fderiv
    have hA : fderiv ℝ A x (I*x) = fderiv ℝ (alpha σ E) (a,x) (0,I*x) := by
      have d := ((alpha_smooth simple.smooth sE).differentiable (by simp) (a,x)).hasFDerivAt.comp x
        ((hasFDerivAt_const a x).prodMk (hasFDerivAt_id x))
      exact DFunLike.congr_fun d.fderiv _
    have productGerm : (fun v => b v*A v) =ᶠ[𝓝 x] fun _ => 1 := by
      filter_upwards [one x xQ,sA.continuous.continuousAt.eventually_ne pos.ne'] with v hv nv
      simp [b,hv,nv]
    have dprod := ((sb.differentiable (by simp) x).hasFDerivAt.mul (sA.differentiable (by simp) x).hasFDerivAt).unique
      ((hasFDerivAt_const 1 x).congr_of_eventuallyEq productGerm)
    have db := DFunLike.congr_fun dprod (I*x)
    change b x * fderiv ℝ A x (I*x) + A x * angularD b x = 0 at db
    rw [hA] at db
    have bx : b x = (A x)⁻¹ := by simp [b,hx]
    rw [bx] at db
    have neq : a ≠ p.1 := fun e => nx (logEq.symm.trans (e ▸ C.log_zero ha))
    have Wval := formula p.1 data neq
    change W (a,p.1) = _ at Wval
    rw [logEq,nr] at Wval
    have hc := flow_angular_column simple sE C ce F hr θ keep
    change fderiv ℝ C.endpoint x (I*x) = _ at hc
    constructor
    · change r*(Real.exp (-σ p.1)*fderiv ℝ g p.1 (I*(Circle.exp p.2:ℂ))) = b x*fderiv ℝ h x (I*x)
      rw [hH,ContinuousLinearMap.comp_apply,hc,map_smul,ey,bx]
      change _ = (A x)⁻¹ * ((r * A x * Real.exp (-σ p.1)) * _)
      field_simp
      rfl
    · change r*(‖C.logMap p.1‖*alpha σ E (a,C.logMap p.1)*W (a,p.1)*g p.1) = -(angularD b x)*h x
      have hvalue : h x = g p.1 := by simp [h,hx,ey]
      rw [logEq,nr,Wval,hvalue]
      change r*(r*A x*(fderiv ℝ (alpha σ E) (a,x) (0,I*x)/(r^2*(A x)^3))*g p.1) = _
      field_simp [hr.ne',pos.ne'] at db ⊢
      linear_combination g p.1*db
  · have g0 := test_germ hB.isClosed off data
    have d0 : fderiv ℝ g p.1 = 0 := by rw [g0.fderiv_eq]; simp
    have H0 : h =ᶠ[𝓝 x] fun _ => 0 := by
      by_cases keep : x ∈ C.velocities
      · have near : Tendsto C.endpoint (𝓝 x) (𝓝 p.1) := (endpoint keep) ▸ C.endpoint_smooth.continuous.continuousAt.tendsto
        filter_upwards [near.eventually g0] with v hv
        simp [h,hv]
      · filter_upwards [zero x keep] with v hv
        simp [h,hv]
    have dH : fderiv ℝ h x = 0 := by rw [H0.fderiv_eq]; simp
    simp [perpendicularSource,d0,angularD,dH,spatialWeight,off p.1 data,H0.self_of_nhds]

end TransportOkaGrauert.ScalarGeneralKernel
