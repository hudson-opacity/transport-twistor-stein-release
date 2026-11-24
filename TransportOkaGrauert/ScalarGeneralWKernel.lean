import TransportOkaGrauert.ScalarGeneralJacobianFactor

/-! # Smooth spatial kernel for the angular average of the normal derivative -/

noncomputable section
namespace TransportOkaGrauert.ScalarGeneralKernel
open Complex Metric Set Filter MeasureTheory SimpleRadialVariation ConformalFrame SimpleDiskTarget
open scoped ContDiff Topology Manifold

theorem jacobian_angular {σ : ℂ → ℝ} (simple : SimpleMetric σ) {E : ℂ × ℂ → ℂ} (sE : ContDiff ℝ ∞ E)
    {a x : ℂ} (C : Coordinates σ a) (ce : C.endpoint = fun w => E (a,w))
    (ret : x ∈ SimpleRadialStar.retained C.endpoint 1) (nx : x ≠ 0) :
    let w := Circle.exp (C.flow (x.arg,‖x‖)).2.1
    0 < alpha σ E (a,x) ∧
    fderiv ℝ C.endpoint x (I*x) = (‖x‖*alpha σ E (a,x)*Real.exp (-σ (E (a,x)))) • (I*(w:ℂ)) := by
  intro w
  obtain ⟨j,jp,rad,ang⟩ := polar_jacobi_with_direction C simple ret nx
  let M := fderiv ℝ C.endpoint x
  let e := Real.exp (-σ (E (a,x)))
  have hr := norm_pos_iff.mpr nx
  have h : wedge (M x) (M (I*x)) = M.det * wedge x (I*x) := wedge_linear M _ _
  have centre : C.endpoint x = E (a,x) := congrFun ce x
  rw [centre] at rad ang
  change fderiv ℝ C.endpoint x x = (‖x‖*e) • (w:ℂ) at rad
  change fderiv ℝ C.endpoint x (I*x) = (j*e) • (I*(w:ℂ)) at ang
  change wedge (fderiv ℝ C.endpoint x x) (fderiv ℝ C.endpoint x (I*x)) = _ at h
  rw [rad,ang,wedge_scale,wedge_I,wedge_I,Complex.normSq_eq_norm_sq,Complex.normSq_eq_norm_sq,Circle.norm_coe,one_pow,mul_one] at h
  have dM : verticalDerivative E (a,x) = M := by rw [verticalDerivative_eq (sE.differentiable (by simp) _),← ce]
  have jac : alpha σ E (a,x) = Real.exp (2*σ (E (a,x))) * M.det := by rw [alpha,dM]
  have cancel : Real.exp (2*σ (E (a,x))) * e^2 = 1 := by
    dsimp [e]; rw [← Real.exp_nat_mul,← Real.exp_add]; ring_nf; simp
  have jj : j = ‖x‖ * alpha σ E (a,x) := by
    rw [jac]
    apply (mul_left_cancel₀ hr.ne')
    calc
      ‖x‖*j = Real.exp (2*σ (E (a,x))) * ((‖x‖*e)*(j*e)) := by
        linear_combination -(‖x‖*j)*cancel
      _ = _ := by rw [h]; ring
  exact ⟨pos_of_mul_pos_right (jj ▸ jp) hr.le,by rw [← jj]; exact ang⟩

private def sourceOpen (E : ℂ × ℂ → ℂ) := ((ball (0:ℂ) 1 ×ˢ univ) ∩ star E)

private theorem source_open {E : ℂ × ℂ → ℂ} (sE : ContDiff ℝ ∞ E) : IsOpen (sourceOpen E) :=
  (isOpen_ball.prod isOpen_univ).inter (open_star sE.continuous)

private theorem alpha_pos {σ : ℂ → ℝ} (simple : SimpleMetric σ) {E : ℂ × ℂ → ℂ} (sE : ContDiff ℝ ∞ E)
    (fam : ∀ a ∈ ball (0:ℂ) 1, ∃ C : Coordinates σ a, C.endpoint = fun v => E (a,v))
    {q : ℂ × ℂ} (hq : q ∈ sourceOpen E) : 0 < alpha σ E q := by
  rcases q with ⟨a,x⟩
  obtain ⟨C,ce⟩ := fam a hq.1.1
  by_cases hx : x = 0
  · subst x
    have dM := verticalDerivative_eq (sE.differentiable (by simp) (a,0))
    rw [← ce,C.endpoint_derivative (mem_ball_zero_iff.mp hq.1.1)] at dM
    rw [alpha,dM]
    apply mul_pos (Real.exp_pos _)
    change 0 < LinearMap.det (Real.exp (-σ a) • (LinearMap.id : ℂ →ₗ[ℝ] ℂ))
    rw [LinearMap.det_smul,Complex.finrank_real_complex,LinearMap.det_id,mul_one]; positivity
  · have ret : x ∈ SimpleRadialStar.retained C.endpoint 1 := fun t ht => by
      rw [ce]; exact (hq.2 t ht).le
    exact (jacobian_angular simple sE C ce ret hx).1

/-- Smooth angular integration-by-parts coefficient on Cartesian velocities.
At the polar face it takes value zero. -/
def angularKernel (σ : ℂ → ℝ) (E : ℂ × ℂ → ℂ) (k : ℂ × ℂ → ℝ) (p : ℂ × ℂ) :=
  fderiv ℝ k p (0,I*p.2) / (2*(alpha σ E p)^4)

theorem angularKernel_zero (σ : ℂ → ℝ) (E : ℂ × ℂ → ℂ) (k : ℂ × ℂ → ℝ) (a : ℂ) :
    angularKernel σ E k (a,0) = 0 := by
  unfold angularKernel
  rw [mul_zero,show ((0,0):ℂ × ℂ) = 0 from rfl,map_zero,zero_div]

/-- The potentially singular angular coefficient equals a smooth Cartesian
function on the first exit chart, including all derivatives at the diagonal. -/
theorem angularKernel_identity {σ : ℂ → ℝ} {E : ℂ × ℂ → ℂ} (hs : ContDiff ℝ ∞ σ) (sE : ContDiff ℝ ∞ E)
    {k : ℂ × ℂ → ℝ} (sk : ContDiff ℝ ∞ k) {a x : ℂ} (nx : x ≠ 0) (pos : 0 < alpha σ E (a,x))
    (eq : (fun p => (alpha σ E p)^2) =ᶠ[𝓝 (a,x)] (fun p => 1+Complex.normSq p.2*k p)) :
    fderiv ℝ (alpha σ E) (a,x) (0,I*x) / (‖x‖^2 * (alpha σ E (a,x))^3) =
      angularKernel σ E k (a,x) := by
  let p := (a,x)
  let v : ℂ × ℂ := (0,I*x)
  let A := alpha σ E
  let line (t : ℝ) : ℂ × ℂ := (a,(Circle.exp t:ℂ)*x)
  have start : line 0 = p := by simp [line,p]
  have dl : HasDerivAt line v 0 := by
    simpa only [Circle.exp_zero,OneMemClass.coe_one,mul_one] using
      (hasDerivAt_const (0:ℝ) a).prodMk ((angle_velocity 0).mul_const x)
  have da := ((alpha_smooth hs sE).differentiable (by simp) (line 0)).hasFDerivAt.comp_hasDerivAt 0 dl
  have dk := (sk.differentiable (by simp) (line 0)).hasFDerivAt.comp_hasDerivAt 0 dl
  have e : (fun t => A (line t)*A (line t)) =ᶠ[𝓝 (0:ℝ)] (fun t => 1+Complex.normSq x*k (line t)) := by
    have near : Tendsto line (𝓝 0) (𝓝 p) := start ▸ dl.continuousAt.tendsto
    filter_upwards [near.eventually eq] with t ht
    have norm : Complex.normSq (line t).2 = Complex.normSq x := by
      change Complex.normSq ((Circle.exp t:ℂ)*x) = _
      rw [map_mul,show Complex.normSq (Circle.exp t:ℂ) = 1 by simp [Complex.normSq_eq_norm_sq],one_mul]
    simpa only [A,pow_two,norm] using ht
  have h := (da.mul da).unique (((dk.const_mul (Complex.normSq x)).const_add 1).congr_of_eventuallyEq e)
  change fderiv ℝ A (line 0) v * A (line 0) + A (line 0) * fderiv ℝ A (line 0) v =
    Complex.normSq x * fderiv ℝ k (line 0) v at h
  rw [start,Complex.normSq_eq_norm_sq] at h
  change fderiv ℝ A p v / (‖x‖^2*(A p)^3) = fderiv ℝ k p v / (2*(A p)^4)
  have ha : A p ≠ 0 := pos.ne'
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr nx
  field_simp
  linear_combination h

private theorem smooth_angularKernel {σ : ℂ → ℝ} (simple : SimpleMetric σ) {E : ℂ × ℂ → ℂ}
    (sE : ContDiff ℝ ∞ E) {k : ℂ × ℂ → ℝ} (sk : ContDiff ℝ ∞ k) {p : ℂ × ℂ} (pos : 0 < alpha σ E p) :
    ContDiffAt ℝ ∞ (angularKernel σ E k) p := by
  have v : ContDiff ℝ ∞ (fun q : ℂ × ℂ => ((0,I*q.2) : ℂ × ℂ)) := contDiff_const.prodMk (contDiff_const.mul contDiff_snd)
  exact (((sk.fderiv_right (m := ∞) (by simp)).clm_apply v).contDiffAt).div
    (contDiffAt_const.mul (((alpha_smooth simple.smooth sE).pow 4).contDiffAt)) (by positivity)

/-- On compact products inside the base disk the angular coefficient has an
ambient smooth representative in the two physical variables. -/
theorem compact_smooth_angular_kernel {σ : ℂ → ℝ} (simple : SimpleMetric σ)
    {A B : Set ℂ} (hA : IsCompact A) (hB : IsCompact B)
    (inA : A ⊆ ball (0:ℂ) 1) (inB : B ⊆ ball (0:ℂ) 1) :
    ∃ E L : ℂ × ℂ → ℂ, ∃ W : ℂ × ℂ → ℝ, ContDiff ℝ ∞ E ∧ ContDiff ℝ ∞ W ∧
      (∀ a ∈ ball (0:ℂ) 1, ∃ C : Coordinates σ a, C.endpoint = (fun v => E (a,v)) ∧ C.logMap = (fun y => L (a,y))) ∧
      (∀ a ∈ A, ∀ y ∈ B, a ≠ y →
        let x := L (a,y)
        W (a,y) = fderiv ℝ (alpha σ E) (a,x) (0,I*x) / (‖x‖^2*(alpha σ E (a,x))^3)) ∧
      ∀ a ∈ A ∩ B, W (a,a) = 0 := by
  obtain ⟨E,L,sE,sL,fam⟩ := joint_coordinates simple
  let base := ball (0:ℂ) 1 ×ˢ ball (0:ℂ) 1
  let log (p : ℂ × ℂ) := (p.1,L p)
  have slog : ContDiffOn ℝ ∞ log base := contDiffOn_fst.prodMk sL
  have cf (a : ℂ) (ha : a ∈ ball (0:ℂ) 1) : ∃ C : Coordinates σ a, C.endpoint = fun v => E (a,v) := by
    obtain ⟨C,c,_⟩ := fam a ha; exact ⟨C,c⟩
  have across : MapsTo log base (sourceOpen E) := by
    rintro ⟨a,y⟩ ⟨ha,hy⟩
    obtain ⟨C,c,t⟩ := fam a ha
    refine ⟨⟨ha,trivial⟩,?_⟩
    have v : C.logMap y ∈ C.velocities := ⟨(C.right y hy).1,show C.endpoint (C.logMap y) ∈ ball (0:ℂ) 1 by rwa [(C.right y hy).2]⟩
    rw [C.velocities_eq_beforeExit simple (mem_ball_zero_iff.mp ha)] at v
    intro r hr
    simpa [log,c,t] using v r hr
  let Q := log '' (A ×ˢ B)
  have sub : A ×ˢ B ⊆ base := prod_mono inA inB
  have compact : IsCompact Q := (hA.prod hB).image_of_continuousOn (slog.continuousOn.mono sub)
  obtain ⟨k,sk,eq⟩ := squared_jacobian_factor simple sE cf (source_open sE) compact.isClosed
    (by rintro _ ⟨p,hp,rfl⟩; exact across (sub hp)) (fun q hq => ⟨hq.1.1,fun r hr => (hq.2 r hr).le⟩)
  let raw (p : ℂ × ℂ) := angularKernel σ E k (log p)
  have sr : ContDiffOn ℝ ∞ raw base := fun p hp =>
    (smooth_angularKernel simple sE sk (alpha_pos simple sE cf (across hp))).comp_contDiffWithinAt p (slog p hp)
  obtain ⟨χ,zero,one,_⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed (𝓘(ℝ,ℂ × ℂ)) (n := ⊤)
    (isOpen_ball.prod isOpen_ball).isClosed_compl (hA.prod hB).isClosed
    (Set.disjoint_left.mpr (fun _ hU hQ => hU (sub hQ)))
  have sχ := contMDiff_iff_contDiff.mp χ.contMDiff
  have same (p : ℂ × ℂ) (hp : p ∈ A ×ˢ B) : χ p = 1 := by
    have ev : ∀ᶠ q in 𝓝 p, χ q = 1 := mem_nhdsSet_iff_forall.mp one p hp
    exact ev.self_of_nhds
  refine ⟨E,L,fun p => χ p*raw p,sE,contDiff_iff_contDiffAt.mpr (fun p => ?_),fam,?_,?_⟩
  · by_cases hp : p ∈ base
    · exact sχ.contDiffAt.mul ((sr p hp).contDiffAt ((isOpen_ball.prod isOpen_ball).mem_nhds hp))
    · apply (contDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq
      filter_upwards [mem_nhdsSet_iff_forall.mp zero p hp] with q hq
      simp [hq]
  · intro a ha y hy ne
    dsimp only
    rw [same (a,y) ⟨ha,hy⟩,one_mul]
    apply (angularKernel_identity simple.smooth sE sk _ (alpha_pos simple sE cf (across (sub ⟨ha,hy⟩))) (eq _ ⟨(a,y),⟨ha,hy⟩,rfl⟩)).symm
    obtain ⟨C,_,t⟩ := fam a (inA ha)
    intro h
    have z := (congrFun t y).trans h
    exact ne (C.endpoint_zero.symm.trans ((congrArg C.endpoint z).symm.trans (C.right y (inB hy)).2))
  · intro a ha
    dsimp only
    rw [same (a,a) ⟨ha.1,ha.2⟩,one_mul]
    obtain ⟨C,_,t⟩ := fam a (inA ha.1)
    change angularKernel σ E k (a,L (a,a)) = 0
    rw [← congrFun t a,C.log_zero (mem_ball_zero_iff.mp (inA ha.1)),angularKernel_zero]

end TransportOkaGrauert.ScalarGeneralKernel
