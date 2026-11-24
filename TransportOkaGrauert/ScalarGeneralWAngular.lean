import TransportOkaGrauert.ScalarGeneralWKernel
import TransportOkaGrauert.ScalarGeneralKernelNormalization

/-! # Angular integration by parts for the finite-time W operator -/

noncomputable section
namespace TransportOkaGrauert.ScalarGeneralKernel
open Complex Metric Set MeasureTheory Filter SimpleDiskTarget SimpleRadialVariation ConformalFrame
open JacobiEnlargement GeodesicFlowExtension ScalarNormalLift
open scoped ContDiff Topology Interval

def turn (r θ : ℝ) : ℂ := r • (Circle.exp θ : ℂ)

theorem turn_deriv (r θ : ℝ) : HasDerivAt (turn r) (I*turn r θ) θ := by
  simpa only [turn,mul_smul_comm] using (angle_velocity θ).const_smul r

theorem turn_smooth (r : ℝ) : ContDiff ℝ ∞ (turn r) := by
  unfold turn
  have sm : ContDiff ℝ ∞ (fun θ : ℝ => (Circle.exp θ : ℂ)) := (Complex.ofRealCLM.contDiff.mul contDiff_const).cexp
  exact (contDiff_const (c := r)).smul sm

def angularD (h : ℂ → ℝ) (x : ℂ) := fderiv ℝ h x (I*x)

theorem angularD_smooth {h : ℂ → ℝ} (sh : ContDiff ℝ ∞ h) : ContDiff ℝ ∞ (angularD h) :=
  (sh.fderiv_right (m := ∞) (by simp)).clm_apply (contDiff_const.mul contDiff_id)

/-- Integration by parts around one complete direction circle, with no
boundary term. -/
theorem angular_parts (r : ℝ) {b h : ℂ → ℝ} (sb : ContDiff ℝ ∞ b) (sh : ContDiff ℝ ∞ h) :
    (∫ θ in (0:ℝ)..2*Real.pi, b (turn r θ) * angularD h (turn r θ)) =
      ∫ θ in (0:ℝ)..2*Real.pi, -(angularD b (turn r θ)) * h (turn r θ) := by
  let G (θ : ℝ) := b (turn r θ) * h (turn r θ)
  have ds {f : ℂ → ℝ} (sf : ContDiff ℝ ∞ f) (θ : ℝ) :
      HasDerivAt (fun t => f (turn r t)) (angularD f (turn r θ)) θ :=
    (sf.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt θ (turn_deriv r θ)
  have d (θ : ℝ) := (ds sb θ).mul (ds sh θ)
  have cb : Continuous (fun θ => angularD b (turn r θ)*h (turn r θ)) := ((angularD_smooth sb).comp (turn_smooth r)).continuous.mul (sh.comp (turn_smooth r)).continuous
  have ch : Continuous (fun θ => b (turn r θ)*angularD h (turn r θ)) := (sb.comp (turn_smooth r)).continuous.mul ((angularD_smooth sh).comp (turn_smooth r)).continuous
  have eq := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := 2*Real.pi) (f := G)
    (fun θ _ => d θ) ((cb.add ch).intervalIntegrable _ _)
  rw [intervalIntegral.integral_add (cb.intervalIntegrable _ _) (ch.intervalIntegrable _ _)] at eq
  have endpt : G (2*Real.pi) = G 0 := by simp [G,turn]
  rw [endpt,sub_self] at eq
  simp_rw [neg_mul,intervalIntegral.integral_neg]
  linarith

theorem rectangle_swap (f : ℝ × ℝ → ℝ) (cf : Continuous f) {T : ℝ} (hT : 0 < T) :
    (∫ θ in (0:ℝ)..2*Real.pi, ∫ r in (0:ℝ)..T, f (θ,r)) =
      ∫ r in (0:ℝ)..T, ∫ θ in (0:ℝ)..2*Real.pi, f (θ,r) := by
  simp_rw [intervalIntegral.integral_of_le hT.le,intervalIntegral.integral_of_le Real.two_pi_pos.le]
  apply integral_integral_swap
  rw [Measure.prod_restrict]
  exact (cf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
    (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)

theorem alpha_on_velocities {σ : ℂ → ℝ} (simple : SimpleMetric σ) {E : ℂ × ℂ → ℂ} (sE : ContDiff ℝ ∞ E)
    {a : ℂ} (ha : ‖a‖ < 1) (C : Coordinates σ a) (ce : C.endpoint = fun v => E (a,v))
    {x : ℂ} (hx : x ∈ C.velocities) : 0 < alpha σ E (a,x) := by
  by_cases hn : x = 0
  · subst x
    have d := verticalDerivative_eq (sE.differentiable (by simp) (a,0))
    rw [← ce,C.endpoint_derivative ha] at d
    rw [alpha,d]
    apply mul_pos (Real.exp_pos _)
    change 0 < LinearMap.det (Real.exp (-σ a) • (LinearMap.id : ℂ →ₗ[ℝ] ℂ))
    rw [LinearMap.det_smul,Complex.finrank_real_complex,LinearMap.det_id,mul_one]; positivity
  · exact (jacobian_angular simple sE C ce hx.1 hn).1

/-- The angular derivative uses the angle of the chosen complete flow even
when the initial coordinate lies beyond the principal argument interval. -/
theorem flow_angular_column {σ : ℂ → ℝ} (simple : SimpleMetric σ) {E : ℂ × ℂ → ℂ} (sE : ContDiff ℝ ∞ E)
    {a : ℂ} (C : Coordinates σ a) (ce : C.endpoint = fun v => E (a,v)) (F : Flow σ)
    {r : ℝ} (hr : 0 < r) (θ : ℝ) (ret : turn r θ ∈ C.velocities) :
    let x := turn r θ
    fderiv ℝ C.endpoint x (I*x) = (r*alpha σ E (a,x)*Real.exp (-σ (F.base (a,θ) r))) •
      (I*(Circle.exp (F.angle (a,θ) r):ℂ)) := by
  intro x
  have nr : ‖x‖ = r := by simp [x,turn,hr.le]
  have nx : x ≠ 0 := norm_ne_zero_iff.mp (nr ▸ hr.ne')
  have repr : r • (Circle.exp x.arg:ℂ) = x := by rw [← nr]; exact polar_angle x
  have rot : Circle.exp x.arg = Circle.exp θ := by
    apply Subtype.ext
    exact (smul_right_injective ℂ hr.ne') repr
  let d := θ-x.arg
  have ed : Circle.exp d = 1 := by simp [d,Circle.exp_sub,rot]
  have move := F.periodic (a,x.arg) d ed r
  have src : (a,x.arg) + ((0,d):State) = (a,θ) := by simp [d]
  rw [src] at move
  have ang : Circle.exp (F.angle (a,x.arg) r) = Circle.exp (F.angle (a,θ) r) := by
    rw [Flow.angle,Flow.angle,move]
    simp [Circle.exp_add,ed]
  have st := state_on_retained C F x.arg r hr (show r • (Circle.exp x.arg:ℂ) ∈ SimpleRadialStar.retained C.endpoint 1 by rw [repr]; exact ret.1)
  have θeq : (C.flow (x.arg,r)).2.1 = F.angle (a,x.arg) r := congrArg Prod.snd st
  have src' := congrArg Prod.fst (state_on_retained C F θ r hr ret.1)
  change (C.flow (θ,r)).1 = F.base (a,θ) r at src'
  rw [C.polar,ce] at src'
  have col := (jacobian_angular simple sE C ce ret.1 nx).2
  change fderiv ℝ C.endpoint x (I*x) = (‖x‖*alpha σ E (a,x)*Real.exp (-σ (E (a,x)))) • (I*(Circle.exp (C.flow (x.arg,‖x‖)).2.1:ℂ)) at col
  rw [nr,θeq,ang] at col
  exact src' ▸ col

theorem density_jacobian {σ : ℂ → ℝ} (simple : SimpleMetric σ) {E : ℂ × ℂ → ℂ} (sE : ContDiff ℝ ∞ E)
    {a : ℂ} (ha : ‖a‖ < 1) (C : Coordinates σ a) (ce : C.endpoint = fun v => E (a,v))
    {y : ℂ} (hy : y ∈ ball (0:ℂ) 1) :
    |(fderiv ℝ C.logMap y).det| * alpha σ E (a,C.logMap y) = Real.exp (2*σ y) := by
  let x := C.logMap y
  have ey : C.endpoint x = y := (C.right y hy).2
  have keep : x ∈ C.velocities := ⟨(C.right y hy).1,show C.endpoint x ∈ ball (0:ℂ) 1 by rwa [ey]⟩
  have p := alpha_on_velocities simple sE ha C ce keep
  have dM := verticalDerivative_eq (sE.differentiable (by simp) (a,x))
  rw [← ce] at dM
  have val : alpha σ E (a,x) = Real.exp (2*σ y) * (fderiv ℝ C.endpoint x).det := by
    rw [alpha,dM,← congrFun ce x,ey]
  rw [val] at p
  have ep := pos_of_mul_pos_right p (Real.exp_pos _).le
  have hd := ((C.log_smooth y hy).contDiffAt (isOpen_ball.mem_nhds hy)).differentiableAt (by simp)
  have comp := (C.endpoint_smooth.differentiable (by simp) x).hasFDerivAt.comp y hd.hasFDerivAt
  have localId : C.endpoint ∘ C.logMap =ᶠ[𝓝 y] id := by filter_upwards [isOpen_ball.mem_nhds hy] with u hu using (C.right u hu).2
  have eq := comp.unique ((hasFDerivAt_id y).congr_of_eventuallyEq localId)
  have det := congrArg (fun M : ℂ →L[ℝ] ℂ => M.det) eq
  change LinearMap.det ((fderiv ℝ C.endpoint x : ℂ →ₗ[ℝ] ℂ).comp (fderiv ℝ C.logMap y : ℂ →ₗ[ℝ] ℂ)) = LinearMap.det LinearMap.id at det
  rw [LinearMap.det_comp,LinearMap.det_id] at det
  change (fderiv ℝ C.endpoint x).det * (fderiv ℝ C.logMap y).det = 1 at det
  have posL := pos_of_mul_pos_right (show 0 < (fderiv ℝ C.endpoint x).det * (fderiv ℝ C.logMap y).det by rw [det]; norm_num) ep.le
  rw [abs_of_pos posL,val]
  linear_combination Real.exp (2*σ y)*det

end TransportOkaGrauert.ScalarGeneralKernel
