import TransportOkaGrauert.ScalarGeneralKernel

/-! # Jointly smooth geodesic logarithms

The exponential is smooth in its centre and its initial velocity. The open
first-exit star identifies its local inverses with the geometric logarithm
already constructed on each disk. -/

noncomputable section
namespace TransportOkaGrauert.ScalarGeneralKernel
open Complex Metric Set Filter SimpleRadialVariation ConformalFrame SimpleRadialStar
open scoped ContDiff Topology

theorem Coordinates.velocities_eq_beforeExit {σ : ℂ → ℝ} {a : ℂ} (C : Coordinates σ a)
    (simple : SimpleDiskTarget.SimpleMetric σ) (ha : ‖a‖ < 1) :
    C.velocities = beforeExit C.endpoint 1 := by
  apply retained_inter_preimage simple (by rwa [C.endpoint_zero])
  intro x hx nx
  let α := x.arg
  have hp := norm_pos_iff.mpr nx
  have repr (t : ℝ) : along C.endpoint x t = (C.flow (α,t)).1 := by
    rw [C.polar]
    change C.endpoint ((t/‖x‖) • x) = _
    calc
      _ = C.endpoint ((t/‖x‖) • (‖x‖ • (Circle.exp α : ℂ))) := by rw [polar_angle x]
      _ = _ := by rw [smul_smul,div_mul_cancel₀ _ hp.ne']
  refine ⟨fun t => (C.flow (α,t)).2.1,?_⟩
  rw [funext repr]
  intro t ht
  have hit : ‖(C.flow (α,t)).1‖ ≤ 1 := by
    rw [← repr]; exact mem_closedBall_zero_iff.mp (along_retained nx hx t ht)
  have eq : fderiv ℝ C.flow (α,t) (0,1) = X σ (C.flow (α,t)) := (C.ode _ hit).self_of_nhds
  have h : HasDerivAt (fun s => C.flow (α,s)) (X σ (C.flow (α,t))) t := by
    rw [← eq]
    exact (C.flow_smooth.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_const t α).prodMk (hasDerivAt_id t))
  have d := h.hasDerivWithinAt (s := Icc 0 ‖x‖)
  rw [(chart_columns σ (C.flow (α,t))).1] at d
  exact ⟨(ContinuousLinearMap.fst ℝ ℂ (ℝ × ℝ)).hasFDerivAt.comp_hasDerivWithinAt t d,
    ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (.snd ℝ ℂ (ℝ × ℝ))).hasFDerivAt.comp_hasDerivWithinAt t d⟩

def star (E : ℂ × ℂ → ℂ) : Set (ℂ × ℂ) :=
  {q | ∀ t ∈ Icc (0:ℝ) 1, ‖E (q.1,t • q.2)‖ < 1}

theorem open_star {E : ℂ × ℂ → ℂ} (h : Continuous E) : IsOpen (star E) := by
  let bad := {u : (ℂ × ℂ) × Icc (0:ℝ) 1 | 1 ≤ ‖E (u.1.1,u.2.val • u.1.2)‖}
  have H : IsClosed bad := isClosed_le continuous_const
    (h.comp ((continuous_fst.comp continuous_fst).prodMk ((continuous_subtype_val.comp continuous_snd).smul
      (continuous_snd.comp continuous_fst)))).norm
  have eq : star E = (Prod.fst '' bad)ᶜ := by ext q; simp [star,bad]
  rw [eq]
  exact (isClosedMap_fst_of_compactSpace bad H).isOpen_compl

/-- The derivative of the map sending a centre and velocity to its centre and
endpoint is invertible wherever the fixed-centre endpoint has a smooth right
inverse. -/
private theorem total_regular {E : ℂ × ℂ → ℂ} (sE : ContDiff ℝ ∞ E) {a x y : ℂ}
    {L : ℂ → ℂ} (sL : DifferentiableAt ℝ L y) (Lx : L y = x)
    (right : (fun z => E (a,L z)) =ᶠ[𝓝 y] id) :
    ∃ e : (ℂ × ℂ) ≃L[ℝ] (ℂ × ℂ), HasFDerivAt (fun q : ℂ × ℂ => (q.1,E q)) e.toContinuousLinearMap (a,x) := by
  let M := fderiv ℝ E (a,x)
  let A := (ContinuousLinearMap.fst ℝ ℂ ℂ).prod M
  have d : HasFDerivAt (fun q : ℂ × ℂ => (q.1,E q)) A (a,x) :=
    (ContinuousLinearMap.fst ℝ ℂ ℂ).hasFDerivAt.prodMk (sE.differentiable (by simp) _).hasFDerivAt
  have s := (sE.differentiable (by simp) (a,L y)).hasFDerivAt.comp y
    ((hasFDerivAt_const a y).prodMk sL.hasFDerivAt)
  have rid := s.unique ((hasFDerivAt_id y).congr_of_eventuallyEq right)
  rw [Lx] at rid
  have surj : Function.Surjective A := by
    rintro ⟨b,v⟩
    let w := v - M (b,0)
    have h := DFunLike.congr_fun rid w
    change M (0,fderiv ℝ L y w) = w at h
    refine ⟨(b,fderiv ℝ L y w),Prod.ext rfl ?_⟩
    change M (b,fderiv ℝ L y w) = v
    rw [show (b,fderiv ℝ L y w) = (b,(0:ℂ)) + (0,fderiv ℝ L y w) by simp,map_add,h]
    dsimp [w]; abel
  exact ⟨ContinuousLinearEquiv.ofBijective A
    (LinearMap.ker_eq_bot.mpr (LinearMap.injective_iff_surjective.mpr surj))
    (LinearMap.range_eq_top.mpr surj),d⟩

/-- One smooth endpoint and one jointly smooth logarithm serve all interior
centres. Their individual slices realize the actual first-exit rays. -/
theorem joint_coordinates {σ : ℂ → ℝ} (simple : SimpleDiskTarget.SimpleMetric σ) :
    ∃ E L : ℂ × ℂ → ℂ, ContDiff ℝ ∞ E ∧
      ContDiffOn ℝ ∞ L (ball (0:ℂ) 1 ×ˢ ball (0:ℂ) 1) ∧
      ∀ a ∈ ball (0:ℂ) 1, ∃ C : Coordinates σ a,
        C.endpoint = (fun v => E (a,v)) ∧ C.logMap = (fun y => L (a,y)) := by
  classical
  let B := ball (0:ℂ) 1
  obtain ⟨E,sE,family⟩ := SimpleRadialSpray.joint_endpoint_and_angle simple.smooth
  have coord (a : ℂ) (ha : a ∈ B) : ∃ C : Coordinates σ a, C.endpoint = (fun v => E (a,v)) := by
    obtain ⟨δ,F,_,sF,zero,init,pol,ode⟩ := family a
    let f (x : ℂ) := E (a,x)
    have sf : ContDiff ℝ ∞ f := sE.comp (contDiff_const.prodMk contDiff_id)
    obtain ⟨L,sL,right,left⟩ := smooth_log_of_geodesic_flow simple f F sf sF
      (by simpa [f,zero] using mem_ball_zero_iff.mp ha) (fun α => by simpa [f,zero] using init α)
      (fun α t => (pol α t).1) ode
    exact ⟨⟨f,F,L,sf,sF,sL,zero,right,left,init,fun α t => (pol α t).1,ode⟩,rfl⟩
  choose C ce using coord
  let L (q : ℂ × ℂ) := if h : q.1 ∈ B then (C q.1 h).logMap q.2 else 0
  have log_eq (a y : ℂ) (h : a ∈ B) : L (a,y) = (C a h).logMap y := dif_pos h
  refine ⟨E,L,sE,?_,fun a ha => ⟨C a ha,ce a ha,funext (fun y => (log_eq a y ha).symm)⟩⟩
  rintro ⟨a,y⟩ ⟨ha,hy⟩
  let P (q : ℂ × ℂ) := (q.1,E q)
  let G (q : ℂ × ℂ) := (q.1,L q)
  let x := (C a ha).logMap y
  obtain ⟨ret,ey⟩ := (C a ha).right y hy
  have Ex : E (a,x) = y := by simpa [ce] using ey
  have sp : (a,x) ∈ star E := by
    have v : x ∈ (C a ha).velocities := ⟨ret,show (C a ha).endpoint ((C a ha).logMap y) ∈ B by rwa [ey]⟩
    rw [(C a ha).velocities_eq_beforeExit simple (mem_ball_zero_iff.mp ha)] at v
    intro t ht
    simpa [ce] using v t ht
  have right : (fun z => E (a,(C a ha).logMap z)) =ᶠ[𝓝 y] id := by
    filter_upwards [isOpen_ball.mem_nhds hy] with z hz
    simpa [ce] using ((C a ha).right z hz).2
  have dL := (((C a ha).log_smooth y hy).contDiffAt (isOpen_ball.mem_nhds hy)).differentiableAt (by simp)
  obtain ⟨e,he⟩ := total_regular sE dL (show (C a ha).logMap y = x from rfl) right
  have sf : ContDiffAt ℝ ∞ P (a,x) := (contDiff_fst.prodMk sE).contDiffAt
  have near : ∀ᶠ q in 𝓝 (a,x), G (P q) = q := by
    have centers : ∀ᶠ q : ℂ × ℂ in 𝓝 (a,x), q.1 ∈ B := continuous_fst.continuousAt.eventually (isOpen_ball.mem_nhds ha)
    filter_upwards [(open_star sE.continuous).mem_nhds sp, centers] with q hq hb
    refine Prod.ext ?_ ?_
    · rfl
    change L (q.1,E q) = q.2
    rw [log_eq q.1 (E q) hb]
    have v : q.2 ∈ beforeExit (C q.1 hb).endpoint 1 := by
      intro t ht
      simpa [ce] using hq t ht
    rw [← (C q.1 hb).velocities_eq_beforeExit simple (mem_ball_zero_iff.mp hb)] at v
    simpa [ce] using (C q.1 hb).left q.2 v.1 v.2
  have loc := sf.to_localInverse he (by simp)
  have eq := (sf.hasStrictFDerivAt' he (by simp)).localInverse_unique (g := G) near
  have sm := contDiffAt_snd.comp (P (a,x)) (loc.congr_of_eventuallyEq eq)
  have target : P (a,x) = (a,y) := Prod.ext rfl Ex
  rw [target] at sm
  exact sm.contDiffWithinAt

end TransportOkaGrauert.ScalarGeneralKernel
