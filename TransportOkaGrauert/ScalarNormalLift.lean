import TransportOkaGrauert.SteinMomentBridge
import TransportOkaGrauert.JacobiEnlargement

/-! # From the spatial normal operator to an invariant angular mean

For compactly supported smooth sources a finite segment running from
outside the disk back to its exterior computes a smooth invariant along
each geodesic through the disk. Its zeroth coefficient is the spatial
normal operator with probability-normalized angular measure. Solving that
operator on smaller disks suffices for the exact Stein endpoints. -/
namespace TransportOkaGrauert.ScalarNormalLift
noncomputable section
open MeasureTheory Metric Set Complex Filter
open SimpleDiskTarget JacobiEnlargement GeodesicFlowExtension PathContinuation
open ScalarGeneralFlow ScalarGeneralTransport ChartCoefficients SteinMomentBridge
open scoped ContDiff Topology Interval

local instance : Fact (0 < 2*Real.pi) := ⟨Real.two_pi_pos⟩

variable {σ : ℂ → ℝ}

def Escapes (F : Flow σ) (T : ℝ) : Prop :=
  ∀ p : State, ‖p.1‖ ≤ 1 → 1 < ‖F.base p T‖ ∧ 1 < ‖F.base p (-T)‖

theorem exists_time (simple : SimpleMetric σ) (F : Flow σ) : ∃ T > 0, Escapes F T := by
  obtain ⟨T,hT,R,hR,_,out⟩ := F.uniform_escape simple
  refine ⟨T,hT,fun p hp => ⟨hR.trans (out p (hp.trans hR.le)),?_⟩⟩
  by_contra! h
  have e := out (F.val (p,-T)) (h.trans hR.le)
  change R < ‖(F.val (F.val (p,-T),T)).1‖ at e
  rw [F.group,neg_add_cancel,F.initial] at e
  linarith

def line (F : Flow σ) (T : ℝ) (g : ℂ → ℂ) (p : State) : ℂ :=
  ∫ s in -T..T, g (F.base p s)

def normal (F : Flow σ) (T : ℝ) (g : ℂ → ℂ) (z : ℂ) : ℂ :=
  (1/(2*Real.pi) : ℝ) • ∫ θ in (0:ℝ)..2*Real.pi, line F T g (z,θ)

/-- Smoothness, flow invariance and the exact ordinary angular integral
are proved together for the same trace. -/
theorem lift (F : Flow σ) (T : ℝ) (esc : Escapes F T) (g : ℂ → ℂ) (sg : ContDiff ℝ ∞ g)
    (off : ∀ z, 1 < ‖z‖ → g z = 0) :
    ∃ h : Trace, ContDiff ℝ ∞ (lifted h) ∧
      (∀ z ∈ PencilLifts.disk, ∀ w, Isothermal.geodesicX σ h z w = 0) ∧
      ∀ z, coefficient h 0 z = normal F T g z := by
  let Φ : SmoothFlow State := ⟨F.val,F.smooth,F.initial,F.group⟩
  let b (p : State) := g p.1
  have sb : ContDiff ℝ ∞ b := sg.comp contDiff_fst
  have hist (p : State) : line F T g p = history Φ b (p,T) - history Φ b (p,-T) := by
    let f (t : ℝ) := g (F.base p t)
    have cf : Continuous f := sg.continuous.comp (continuous_fst.comp (F.smooth.continuous.comp
      (continuous_const.prodMk continuous_id)))
    change (∫ t in -T..T, f t) = (∫ t in (0:ℝ)..T, f (-t)) - ∫ t in (0:ℝ)..-T, f (-t)
    rw [intervalIntegral.integral_comp_neg,intervalIntegral.integral_comp_neg,neg_neg,neg_zero]
    rw [sub_eq_add_neg,← intervalIntegral.integral_symm T 0,intervalIntegral.integral_add_adjacent_intervals (cf.intervalIntegrable _ _) (cf.intervalIntegrable _ _)]
  have smooth : ContDiff ℝ ∞ (line F T g) := by
    rw [funext hist]
    exact ((history_smooth Φ sb).comp (contDiff_id.prodMk contDiff_const)).sub
      ((history_smooth Φ sb).comp (contDiff_id.prodMk contDiff_const))
  have same {a b : ℝ} (ha : Circle.exp a = Circle.exp b) (z : ℂ) : line F T g (z,a) = line F T g (z,b) := by
    have pe : Circle.exp (a-b) = 1 := by rw [sub_eq_add_neg,Circle.exp_add,Circle.exp_neg,ha,mul_inv_cancel]
    apply intervalIntegral.integral_congr
    intro s _
    have eq := congrArg Prod.fst (F.periodic (z,b) (a-b) pe s)
    simpa [Flow.base,show (z,b)+(0,a-b) = (z,a) by ext <;> simp] using congrArg g eq
  let h (z : ℂ) (w : Circle) := line F T g (z,(w:ℂ).arg)
  have liftEq : lifted h = line F T g := by
    funext q
    exact same (Circle.exp_arg _) _
  refine ⟨h,liftEq ▸ smooth,?_,?_⟩
  · intro z hz w
    let p : State := (z,(w:ℂ).arg)
    have hp : ‖p.1‖ ≤ 1 := (mem_ball_zero_iff.mp hz).le
    have eq := F.germ hp
    have ev : chartVector F.factor p = chartVector σ p := by
      simp [chartVector,Isothermal.angularDrift,eq.eq_of_nhds,eq.fderiv_eq]
    have flow := F.ode p 0
    rw [F.initial,ev] at flow
    have deriv := (smooth.differentiable (by simp) p).hasFDerivAt.comp_hasDerivAt_of_eq 0 flow (F.initial p).symm
    have shift (s : ℝ) : line F T g (F.val (p,s)) = history Φ b (p,T-s) - history Φ b (p,-T-s) := by
      rw [hist,show F.val (p,s) = Φ.val (p,s) from rfl,
        history_advance Φ sb.continuous,history_advance Φ sb.continuous]
      abel
    have hd (d : ℝ) : HasDerivAt (fun s : ℝ => history Φ b (p,d-s)) (-(b (Φ.val (p,-d)))) 0 := by
      have ds := (history_derivative Φ sb.continuous p (d-0)).scomp 0 ((hasDerivAt_const (0:ℝ) d).sub (hasDerivAt_id 0))
      simpa using ds
    have endval := (hd T).sub (hd (-T))
    have zero : HasDerivAt (fun s => line F T g (F.val (p,s))) 0 0 := by
      rw [funext shift]
      have fwd : b (Φ.val (p,T)) = 0 := off _ (esc p hp).1
      have back : b (Φ.val (p,-T)) = 0 := off _ (esc p hp).2
      simpa only [Pi.sub_apply,neg_neg,fwd,back,neg_zero,sub_self] using endval
    have v := deriv.unique zero
    have exp : Circle.exp (w:ℂ).arg = w := Circle.exp_arg _
    have regular : ContDiff ℝ ∞ (lifted h) := liftEq ▸ smooth
    rw [← exp,geodesicX_eq_chart_derivative _ _ _ _ (regular.differentiable (by simp) p)]
    change fderiv ℝ (lifted h) p (chartVector σ p) = 0
    rwa [liftEq]
  · intro z
    unfold coefficient normal
    rw [fourierCoeff_eq_intervalIntegral _ _ 0,zero_add]
    congr 1
    apply intervalIntegral.integral_congr
    intro t _
    simpa [ChartModes.toCircle_angle] using congrFun liftEq (z,t)

/-- The spatial inversion problem is posed only on a disk strictly inside the
domain of integration. Sources are smooth through its outer boundary. -/
def SmoothNormalRange : Prop := ∀ σ : ℂ → ℝ, SimpleMetric σ → ∀ a : ℂ → ℂ, ContDiff ℝ ∞ a →
  ∀ r : ℝ, 0 < r → r < 1 → ∃ (F : Flow σ) (T : ℝ), 0 < T ∧ Escapes F T ∧
    ∃ g : ℂ → ℂ, ContDiff ℝ ∞ g ∧ (∀ z, 1 < ‖z‖ → g z = 0) ∧
      ∀ z ∈ ball (0:ℂ) r, normal F T g z = a z

theorem universal_of_normal_range (range : SmoothNormalRange) :
    ChartStein.GeneralSimpleSurfaceStatement ∧ ManifoldStein.GeneralManifoldStatement := by
  have mean : CompactInteriorMeanStatement := by
    intro τ simple a sa r hr hs
    obtain ⟨F,T,_,esc,g,sg,off,eq⟩ := range τ simple a sa r hr hs
    obtain ⟨h,sh,inv,avg⟩ := lift F T esc g sg off
    exact ⟨h,fun _ _ _ => sh.contDiffAt,inv,fun z hz => (avg z).trans (eq z hz)⟩
  have chart : ChartStein.GeneralSimpleSurfaceStatement :=
    fun _ s => chart_of_mean s (mean_from_compact mean s)
  exact ⟨chart,ManifoldStein.manifold_of_chart chart⟩

end
end TransportOkaGrauert.ScalarNormalLift
