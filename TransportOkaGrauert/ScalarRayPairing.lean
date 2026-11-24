import TransportOkaGrauert.ScalarPestovEstimate

/-! # Reciprocity for the smooth geodesic normal operator

The product of a forward primitive and a backward primitive has support over
the disk. Integrating its speed derivative gives the forward/backward
adjoint relation without choosing boundary coordinates at tangent rays.
-/
noncomputable section
namespace TransportOkaGrauert.ScalarRayPairing
open SimpleDiskTarget JacobiEnlargement GeodesicFlowExtension ScalarGeneralFlow PathContinuation
open FrameLevi ConformalFrame Set MeasureTheory Filter Complex
open scoped ContDiff Topology Interval

abbrev AngleTrace := State → ℝ
def period (f : AngleTrace) := ∀ p : State, f (p+(0,2*Real.pi)) = f p
def supported (f : AngleTrace) := ∀ p : State, 1 < ‖p.1‖ → f p = 0

structure Window {σ : ℂ → ℝ} (F : Flow σ) where
  T : ℝ
  pos : 0 < T
  out : ∀ p : State, ‖p.1‖ ≤ 1 → 1 < ‖F.base p T‖

variable {σ : ℂ → ℝ} (F : Flow σ)

theorem exists_window (simple : SimpleMetric σ) : Nonempty (Window F) := by
  obtain ⟨T,hT,R,hR,_,out⟩ := F.uniform_escape simple
  exact ⟨T,hT,fun p hp => hR.trans (out p (hp.trans hR.le))⟩

def flow : SmoothFlow State := ⟨F.val,F.smooth,F.initial,F.group⟩
def past (W : Window F) (f : AngleTrace) (p : State) := history (flow F) f (p,W.T)
def future (W : Window F) (f : AngleTrace) (p : State) := -history (flow F) f (p,-W.T)
def full (W : Window F) (f : AngleTrace) := past F W f + future F W f

def speed := along (chartVector F.factor)

theorem history_speed {f : AngleTrace} (hf : ContDiff ℝ ∞ f) (p : State) (s : ℝ) :
    speed F (fun q => history (flow F) f (q,s)) p = f p - f (F.val (p,-s)) := by
  let Φ := flow F
  let U := fun q : State => history Φ f (q,s)
  have hu : ContDiff ℝ ∞ U := (history_smooth Φ hf).comp (contDiff_id.prodMk contDiff_const)
  have d := (hu.differentiable (by simp) (F.val (p,0))).hasFDerivAt.comp_hasDerivAt 0 (F.ode p 0)
  rw [F.initial] at d
  have shift (t : ℝ) : U (F.val (p,t)) = history Φ f (p,s-t) - history Φ f (p,-t) :=
    history_advance Φ hf.continuous p t s
  have d₁ := (history_derivative Φ hf.continuous p (s-0)).scomp 0
    (by simpa using (hasDerivAt_const (0:ℝ) s).sub (hasDerivAt_id 0) :
      HasDerivAt (fun t : ℝ => s-t) (-1) 0)
  have d₂ := (history_derivative Φ hf.continuous p (-0)).scomp 0
    (by simpa using (hasDerivAt_id (0:ℝ)).neg : HasDerivAt (fun t : ℝ => -t) (-1) 0)
  have v : HasDerivAt (fun t => U (F.val (p,t))) (f p - f (F.val (p,-s))) 0 := by
    rw [funext shift]
    convert d₁.sub d₂ using 1
    simp [Φ,flow,F.initial]; ring
  exact d.unique v

theorem past_smooth (W : Window F) {f : AngleTrace} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (past F W f) := (history_smooth (flow F) hf).comp (contDiff_id.prodMk contDiff_const)

theorem future_smooth (W : Window F) {f : AngleTrace} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (future F W f) :=
  ((history_smooth (flow F) hf).comp (contDiff_id.prodMk contDiff_const)).neg

theorem window_derivatives (W : Window F) {f : AngleTrace} (hf : ContDiff ℝ ∞ f) (zf : supported f)
    (p : State) (hp : ‖p.1‖ ≤ 1) :
    speed F (past F W f) p = f p ∧ speed F (future F W f) p = -f p := by
  have forward := W.out p hp
  have back : 1 < ‖F.base p (-W.T)‖ := by
    by_contra! e
    have o := W.out (F.val (p,-W.T)) e
    simp [Flow.base,F.group,F.initial,not_lt_of_ge hp] at o
  refine ⟨by simpa only [past,zf _ back,sub_zero] using history_speed F hf p W.T,?_⟩
  change fderiv ℝ (fun q => -history (flow F) f (q,-W.T)) p (chartVector F.factor p) = _
  rw [fderiv_fun_neg,ContinuousLinearMap.neg_apply]
  change -speed F (fun q => history (flow F) f (q,-W.T)) p = _
  simp [history_speed F hf, zf _ forward]

private theorem history_period {f : AngleTrace} (pf : period f) (s : ℝ) :
    period (fun p => history (flow F) f (p,s)) := by
  intro p
  unfold history
  apply intervalIntegral.integral_congr
  intro t _
  change f (F.val (p+(0,2*Real.pi),-t)) = _
  rw [F.periodic p _ Circle.exp_two_pi,pf]
  rfl

theorem past_period (W : Window F) {f : AngleTrace} (pf : period f) : period (past F W f) :=
  history_period F pf W.T

theorem future_period (W : Window F) {f : AngleTrace} (pf : period f) : period (future F W f) :=
  fun p => congrArg Neg.neg (history_period F pf (-W.T) p)

theorem no_straddle (p : State) (hp : 1 < ‖p.1‖) :
    (∀ t : ℝ, t ≤ 0 → 1 < ‖F.base p t‖) ∨ (∀ t : ℝ, 0 ≤ t → 1 < ‖F.base p t‖) := by
  by_contra! h
  obtain ⟨⟨a,ha,ia⟩,b,hb,ib⟩ := h
  have bad := GeodesicNonreturn.stays_in_disk (F.geo p (Icc a b)) ia ib
    (fun q hq => F.convex q hq.le) 0 ⟨ha,hb⟩
  simp [Flow.base,F.initial,not_le_of_gt hp] at bad

theorem future_eq (W : Window F) (f : AngleTrace) (p : State) :
    future F W f p = ∫ s in 0..W.T, f (F.val (p,s)) := by
  change -(∫ t in 0..-W.T, (fun s => f (F.val (p,s))) (-t)) = _
  have e := intervalIntegral.integral_comp_neg (fun s => f (F.val (p,s))) (a := 0) (b := -W.T)
  rw [e,neg_neg,neg_zero,intervalIntegral.integral_symm 0 W.T,neg_neg]

theorem pair_supported (W : Window F) {f g : AngleTrace} (zf : supported f) (zg : supported g) :
    supported (fun p => future F W f p * past F W g p) := by
  intro p hp
  rcases no_straddle F p hp with h|h
  · have e : past F W g p = 0 := by
      change (∫ t in 0..W.T, g (F.val (p,-t))) = 0
      calc
        _ = ∫ _t in 0..W.T, (0:ℝ) := intervalIntegral.integral_congr fun t ht =>
          zg _ (h _ (neg_nonpos.mpr ((uIcc_of_le W.pos.le ▸ ht).1)))
        _ = 0 := intervalIntegral.integral_zero
    simp [e]
  · have e : future F W f p = 0 := by
      rw [future_eq]
      calc
        _ = ∫ _t in 0..W.T, (0:ℝ) := intervalIntegral.integral_congr fun t ht =>
          zf _ (h _ ((uIcc_of_le W.pos.le ▸ ht).1))
        _ = 0 := intervalIntegral.integral_zero
    simp [e]

def integral (f : AngleTrace) := ScalarLiouville.integral F.factor (f ∘ PolarCollar.direction)

theorem integral_sub {f g : AngleTrace} (hf : Continuous f) (hg : Continuous g) :
    integral F (f-g) = integral F f - integral F g := by
  have h := ScalarLiouville.int_linear F.smoothFactor.continuous
    (hf.comp PolarCollar.direction.continuous) (hg.comp PolarCollar.direction.continuous)
    (continuous_const (y := (0:ℝ)))
  simpa only [integral,Pi.sub_apply,Function.comp_apply,add_zero,
    (show ScalarLiouville.integral F.factor (fun _ => 0) = 0 from by simp [ScalarLiouville.integral])] using h

theorem integral_speed {f : AngleTrace} (hf : ContDiff ℝ ∞ f) (pf : period f) (zf : supported f) :
    integral F (speed F f) = 0 := by
  let u := f ∘ PolarCollar.direction
  have hX := ScalarLiouville.integral_X F.smoothFactor (hf.comp PolarCollar.direction.contDiff)
    (show ScalarLiouville.periodic u from fun p => pf (PolarCollar.direction p))
    (show ScalarLiouville.zero_exterior u from fun p hp => zf _ hp)
  have eq : (speed F f) ∘ PolarCollar.direction = along (X F.factor) u := by
    funext p
    have push : PolarCollar.direction (X F.factor p) = chartVector F.factor (PolarCollar.direction p) :=
      congrFun (PhysicalJacobiWeight.projected_X F.factor) (PolarCollar.direction p)
    change _ = fderiv ℝ (f ∘ PolarCollar.direction) p (X F.factor p)
    rw [fderiv_comp p (hf.differentiable (by simp) _) PolarCollar.direction.differentiableAt,
      ContinuousLinearMap.fderiv,ContinuousLinearMap.comp_apply,push]
    rfl
  simpa only [integral,eq] using hX

/-- Forward and backward ray integration are adjoints for the actual
conformal Liouville density. -/
theorem adjoint (W : Window F) {f g : AngleTrace}
    (hf : ContDiff ℝ ∞ f) (pf : period f) (zf : supported f)
    (hg : ContDiff ℝ ∞ g) (pg : period g) (zg : supported g) :
    integral F (fun p => f p * past F W g p) = integral F (fun p => future F W f p * g p) := by
  let A := fun p => future F W f p * past F W g p
  let a := fun p => f p * past F W g p
  let b := fun p => future F W f p * g p
  have hA : ContDiff ℝ ∞ A := (future_smooth F W hf).mul (past_smooth F W hg)
  have zA : supported A := pair_supported F W zf zg
  have pA : period A := fun p => by simp [A,future_period F W pf p,past_period F W pg p]
  have der : speed F A = b-a := by
    funext p
    by_cases h : ‖p.1‖ ≤ 1
    · unfold speed along A
      rw [fderiv_fun_mul ((future_smooth F W hf).differentiable (by simp) p) ((past_smooth F W hg).differentiable (by simp) p)]
      simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
      have u := (window_derivatives F W hf zf p h).2
      have v := (window_derivatives F W hg zg p h).1
      dsimp [speed,along] at u v
      simp [a,b,u,v]; ring
    · have ho := lt_of_not_ge h
      have e : A =ᶠ[𝓝 p] fun _ => 0 := (continuous_fst.norm.continuousAt.eventually_const_lt ho).mono
        (fun q hq => zA q hq)
      simp [speed,along,e.fderiv_eq,a,b,zf _ ho,zg _ ho]
  have z := integral_speed F hA pA zA
  rw [der,integral_sub F (f := b) (g := a) ((future_smooth F W hf).continuous.mul hg.continuous)
    (hf.continuous.mul (past_smooth F W hg).continuous)] at z
  exact (sub_eq_zero.mp z).symm

theorem full_smooth (W : Window F) {f : AngleTrace} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (full F W f) := (past_smooth F W hf).add (future_smooth F W hf)

theorem full_period (W : Window F) {f : AngleTrace} (pf : period f) : period (full F W f) :=
  fun p => by simp [full,past_period F W pf p,future_period F W pf p]

theorem full_eq (W : Window F) {f : AngleTrace} (hf : Continuous f) (p : State) :
    full F W f p = ∫ t in -W.T..W.T, f (F.val (p,t)) := by
  have ct : Continuous (fun t : ℝ => f (F.val (p,t))) := hf.comp (F.smooth.continuous.comp (continuous_const.prodMk continuous_id))
  have pe : past F W f p = ∫ t in -W.T..0, f (F.val (p,t)) := by
    simpa only [past,flow,history,neg_zero] using
      (intervalIntegral.integral_comp_neg (fun s => f (F.val (p,s))) (a := 0) (b := W.T))
  change past F W f p + future F W f p = _
  rw [pe,future_eq]
  exact intervalIntegral.integral_add_adjacent_intervals (ct.intervalIntegrable _ _) (ct.intervalIntegrable _ _)

def orbit_constant (h : AngleTrace) :=
  ∀ p : State, ‖p.1‖ ≤ 1 → ∀ t : ℝ, ‖F.base p t‖ ≤ 1 → h (F.val (p,t)) = h p

theorem full_constant (W : Window F) {f : AngleTrace} (hf : ContDiff ℝ ∞ f) (zf : supported f) :
    orbit_constant F (full F W f) := by
  have hs := full_smooth F W hf
  have forward (p : State) (hp : ‖p.1‖ ≤ 1) (t : ℝ) (ht : 0 ≤ t) (he : ‖F.base p t‖ ≤ 1) :
      full F W f (F.val (p,t)) = full F W f p := by
    have stay := F.stays le_rfl hp he
    have d (s : ℝ) (h : s ∈ Icc 0 t) : HasDerivAt (fun u => full F W f (F.val (p,u))) 0 s := by
      have g := (hs.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt s (F.ode p s)
      apply g.congr_deriv
      have e := window_derivatives F W hf zf (F.val (p,s)) (stay s h)
      change fderiv ℝ (past F W f + future F W f) _ _ = _
      rw [fderiv_add ((past_smooth F W hf).differentiable (by simp) _) ((future_smooth F W hf).differentiable (by simp) _),
        ContinuousLinearMap.add_apply]
      exact (congrArg₂ (·+·) e.1 e.2).trans (add_neg_cancel _)
    have ct : Continuous (fun u => full F W f (F.val (p,u))) :=
      hs.continuous.comp (F.smooth.continuous.comp (continuous_const.prodMk continuous_id))
    have eq := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht ct.continuousOn
      (fun u hu => d u (Ioo_subset_Icc_self hu)) (intervalIntegrable_const (c := (0:ℝ)))
    simpa [F.initial,sub_eq_zero] using eq.symm
  intro p hp t he
  rcases le_total 0 t with ht|ht
  · exact forward p hp t ht he
  · have ee : ‖F.base (F.val (p,t)) (-t)‖ ≤ 1 := by simpa [Flow.base,F.group,F.initial] using hp
    simpa [F.group,F.initial] using (forward (F.val (p,t)) he (-t) (neg_nonneg.mpr ht) ee).symm

theorem extract_constant (W : Window F) {f h : AngleTrace} (hf : Continuous f) (hh : Continuous h)
    (zf : supported f) (inv : orbit_constant F h) {p : State} (hp : ‖p.1‖ ≤ 1) :
    full F W (fun q => f q * h q) p = full F W f p * h p := by
  rw [full_eq F W (f := fun q => f q * h q) (hf.mul hh),full_eq F W hf,← intervalIntegral.integral_mul_const]
  apply intervalIntegral.integral_congr
  intro t _
  change f (F.val (p,t)) * h (F.val (p,t)) = f (F.val (p,t)) * h p
  by_cases e : ‖F.base p t‖ ≤ 1
  · rw [inv p hp t e]
  · simp [zf _ (lt_of_not_ge e)]

theorem integral_add {f g : AngleTrace} (hf : Continuous f) (hg : Continuous g) :
    integral F (f+g) = integral F f + integral F g := by
  have z := ScalarLiouville.int_linear F.smoothFactor.continuous (hf.comp PolarCollar.direction.continuous)
    (continuous_const (y := (0:ℝ))) (hg.comp PolarCollar.direction.continuous)
  simpa only [integral,Pi.add_apply,Function.comp_apply,sub_zero,
    (show ScalarLiouville.integral F.factor (fun _ => 0) = 0 from by simp [ScalarLiouville.integral])] using z

theorem symmetric (W : Window F) {f g : AngleTrace}
    (hf : ContDiff ℝ ∞ f) (pf : period f) (zf : supported f)
    (hg : ContDiff ℝ ∞ g) (pg : period g) (zg : supported g) :
    integral F (fun p => f p * full F W g p) = integral F (fun p => full F W f p * g p) := by
  have a := adjoint F W hf pf zf hg pg zg
  have b := adjoint F W hg pg zg hf pf zf
  have b' : integral F (fun p => f p * future F W g p) = integral F (fun p => past F W f p * g p) := by
    simpa only [mul_comm] using b.symm
  change integral F (fun p => f p * (past F W g p + future F W g p)) =
    integral F (fun p => (past F W f p + future F W f p) * g p)
  simp only [mul_add,add_mul]
  exact (integral_add F (hf.continuous.mul (past_smooth F W hg).continuous)
    (hf.continuous.mul (future_smooth F W hg).continuous)).trans
      ((congrArg₂ (·+·) a b').trans ((add_comm _ _).trans (integral_add F
        ((past_smooth F W hf).continuous.mul hg.continuous)
        ((future_smooth F W hf).continuous.mul hg.continuous)).symm))

end TransportOkaGrauert.ScalarRayPairing
