import TransportOkaGrauert.ScalarHilbertParametrix
import TransportOkaGrauert.ScalarInvariantSeparation

/-! # Even primitive and its actual perpendicular-ray average -/
namespace TransportOkaGrauert.ScalarWPrimitive
noncomputable section
open Complex MeasureTheory Metric Set Filter AddCircle
open SimpleDiskTarget JacobiEnlargement GeodesicFlowExtension ScalarRayPairing ScalarGeneralTransport
open PathContinuation ChartCoefficients ScalarHilbertParametrix
open scoped ContDiff Topology Interval
local instance : Fact (0 < 2*Real.pi) := ⟨Real.two_pi_pos⟩

def source (σ a : ℂ → ℝ) (p : State) :=
  Real.exp (-σ p.1) * fderiv ℝ a p.1 (I * (Circle.exp p.2 : ℂ))

def Wvalue (σ : ℂ → ℝ) (F : Flow σ) (T : ℝ) (a : ℂ → ℝ) (z : ℂ) :=
  -(1/(2*Real.pi)) * ∫ θ in (0:ℝ)..2*Real.pi, ∫ t in (0:ℝ)..T, source σ a (F.val ((z,θ),t))

def half (p : State) : State := p + (0,Real.pi)

private theorem halfVector (σ : ℂ → ℝ) (p : State) : chartVector σ (half p) = -chartVector σ p := by
  have e : (Circle.exp (half p).2 : ℂ) = -(Circle.exp p.2 : ℂ) := by simp [half,Circle.exp_add]
  have e' : (half p).1 = p.1 := by simp [half]
  rw [chartVector,chartVector]
  simp only [e,e',Isothermal.angularDrift,neg_re,neg_im]
  ext <;> simp [Complex.real_smul]
  ring

private theorem halfSource (σ a : ℂ → ℝ) (p : State) : source σ a (half p) = -source σ a p := by
  simp [half,source,Circle.exp_add]

private theorem source_smooth {σ a : ℂ → ℝ} (sσ : ContDiff ℝ ∞ σ) (sa : ContDiff ℝ ∞ a) :
    ContDiff ℝ ∞ (source σ a) := by
  have ang : ContDiff ℝ ∞ (fun p : State => (Circle.exp p.2 : ℂ)) := by
    simp only [Circle.coe_exp]
    exact ((Complex.ofRealCLM.contDiff.comp contDiff_snd).mul contDiff_const).cexp
  exact ((sσ.comp contDiff_fst).neg.exp).mul (((sa.fderiv_right (m := ∞) (by simp)).comp
    contDiff_fst).clm_apply (contDiff_const.mul ang))

private theorem zero_for_odd (h : Trace) (z : ℂ)
    (even : ∀ w, h z (w*Circle.exp Real.pi) = h z w) (k : ℤ) (hk : k = 1 ∨ k = -1) :
    coefficient h k z = 0 := by
  let a : DiskSeries.Angle := (Real.pi : ℝ)
  have pa : a.toCircle = Circle.exp Real.pi := ChartModes.toCircle_angle _
  let f (t : DiskSeries.Angle) := fourier (-k) t * h z t.toCircle
  have neg (t : DiskSeries.Angle) : f (t+a) = -f t := by
    have char : fourier (-k) (t+a) = -fourier (-k) t := by
      have na : (-a).toCircle = Circle.exp (-Real.pi) := by
        change AddCircle.toCircle (T := 2*Real.pi) (-((Real.pi : ℝ) : DiskSeries.Angle)) = _
        rw [← AddCircle.coe_neg]
        exact ChartModes.toCircle_angle _
      rcases hk with rfl|rfl <;> simp [AddCircle.toCircle_add,pa,na,Circle.exp_neg]
    simp only [f,char,AddCircle.toCircle_add,pa,even,neg_mul]
  exact integral_eq_zero_of_add_right_eq_neg (μ := AddCircle.haarAddCircle) neg

theorem primitive {σ : ℂ → ℝ} (simple : SimpleMetric σ) (F : Flow σ) (W : Window F)
    (a : ℂ → ℝ) (sa : ContDiff ℝ ∞ a) (off : ∀ z, 1 < ‖z‖ → a z = 0) :
    ∃ u : Trace, ContDiff ℝ ∞ (lifted u) ∧
      (∀ z ∈ PencilLifts.disk, ∀ w, Isothermal.geodesicX σ u z w = perp σ (fun y => (a y : ℂ)) z w) ∧
      (∀ z, coefficient u 0 z = (Wvalue σ F W.T a z : ℂ)) ∧
      (∀ z, coefficient u (-1) z = 0 ∧ coefficient u 1 z = 0) := by
  let q := source σ a
  have sq := source_smooth simple.smooth sa
  have oq : supported q := by
    intro p hp
    have eq : a =ᶠ[𝓝 p.1] fun _ => 0 := (continuous_norm.continuousAt.eventually_const_lt hp).mono
      fun z hz => off z hz
    simp [q,source,eq.fderiv_eq]
  have pq : period q := by intro p; simp [q,source,Circle.exp_add]
  let B : AngleTrace := fun p => -(future F W q p)
  have sB : ContDiff ℝ ∞ B := (future_smooth F W sq).neg
  have pB : period B := fun p => congrArg Neg.neg (future_period F W pq p)
  have der (p : State) (hp : ‖p.1‖ ≤ 1) : fderiv ℝ B p (chartVector σ p) = q p := by
    have e := F.germ hp
    have vec : chartVector F.factor p = chartVector σ p := by simp [chartVector,Isothermal.angularDrift,e.eq_of_nhds,e.fderiv_eq]
    change fderiv ℝ (fun p => -(future F W q p)) p _ = _
    rw [fderiv_fun_neg,ContinuousLinearMap.neg_apply,← vec]
    change -(speed F (future F W q) p) = _
    rw [(window_derivatives F W sq oq p hp).2,neg_neg]
  let A (p : State) := (1/2:ℝ)*(B p + B (half p))
  have shalf : ContDiff ℝ ∞ half := contDiff_id.add contDiff_const
  have sA : ContDiff ℝ ∞ A := contDiff_const.mul (sB.add (sB.comp shalf))
  have aHalf (p : State) : A (half p) = A p := by
    have same : half (half p) = p+(0,2*Real.pi) := by ext <;> simp [half]; ring
    simp only [A,same,pB p]; rw [add_comm]
  have pA (z : ℂ) : Function.Periodic (fun t => A (z,t)) (2*Real.pi) := by
    intro t
    have e : (z,t+2*Real.pi) = half (half (z,t)) := by ext <;> simp [half]; ring
    change A (z,t+2*Real.pi) = A (z,t)
    rw [e,aHalf,aHalf]
  let u (z : ℂ) (w : Circle) : ℂ := A (z,(w:ℂ).arg)
  have liftAt (z : ℂ) (t : ℝ) : u z (Circle.exp t) = (A (z,t) : ℂ) := by
    obtain ⟨m,hm⟩ := Circle.exp_eq_exp.mp (Circle.exp_arg (Circle.exp t))
    change (A (z,(Circle.exp t:ℂ).arg) : ℂ) = _
    rw [hm]
    exact congrArg Complex.ofReal ((pA z).int_mul m t)
  have liftEq : lifted u = ofRealCLM ∘ A := funext fun p => liftAt p.1 p.2
  have su : ContDiff ℝ ∞ (lifted u) := liftEq ▸ ofRealCLM.contDiff.comp sA
  refine ⟨u,su,?_,?_,?_⟩
  · intro z hz w
    let p : State := (z,(w:ℂ).arg)
    have hp : ‖p.1‖ ≤ 1 := (mem_ball_zero_iff.mp hz).le
    have eq : Circle.exp p.2 = w := Circle.exp_arg _
    have dh := (sB.differentiable (by simp) (half p)).hasFDerivAt.comp p
      ((hasFDerivAt_id p).add_const ((0,Real.pi):State))
    have hder : fderiv ℝ (B ∘ half) p (chartVector σ p) = q p := by
      rw [show fderiv ℝ (B ∘ half) p = _ from dh.fderiv]
      change fderiv ℝ B (half p) (chartVector σ p) = _
      rw [show chartVector σ p = -(chartVector σ (half p)) by rw [halfVector,neg_neg],map_neg,
        der (half p) (by simpa [half] using hp)]
      simp [q,halfSource]
    have da := (((sB.differentiable (by simp) p).hasFDerivAt.add (sB.comp shalf |>.differentiable (by simp) p).hasFDerivAt).const_mul (1/2:ℝ)).fderiv
    have ad : fderiv ℝ A p (chartVector σ p) = q p := by
      change fderiv ℝ (fun y => (1/2:ℝ)*(B + B ∘ half) y) p _ = _
      rw [da,ContinuousLinearMap.smul_apply,ContinuousLinearMap.add_apply,der p hp,hder,smul_eq_mul]
      ring
    rw [← eq,geodesicX_eq_chart_derivative _ _ _ _ (su.differentiable (by simp) p)]
    change fderiv ℝ (lifted u) p (chartVector σ p) = _
    rw [liftEq,fderiv_comp p ofRealCLM.differentiableAt (sA.differentiable (by simp) p),
      ContinuousLinearMap.fderiv,ContinuousLinearMap.comp_apply,ad]
    have df := ofRealCLM.hasFDerivAt.comp z (sa.differentiable (by simp) z).hasFDerivAt
    change ofRealCLM (q p) = (Real.exp (-σ z):ℂ) * fderiv ℝ (ofRealCLM ∘ a) z _
    rw [df.fderiv]
    simp [q,source,p]
  · intro z
    rw [coefficient,fourierCoeff_eq_intervalIntegral _ _ 0,zero_add]
    simp only [neg_zero,fourier_zero,one_smul,ChartModes.toCircle_angle,liftAt]
    have cont (R : State → ℝ) (sR : ContDiff ℝ ∞ R) : Continuous (fun t : ℝ => R (z,t)) :=
      sR.continuous.comp (continuous_const.prodMk continuous_id)
    have iA := (cont A sA).intervalIntegrable (μ := volume) 0 (2*Real.pi)
    change _ • (∫ t in (0:ℝ)..2*Real.pi, ofRealCLM (A (z,t))) = _
    rw [ofRealCLM.intervalIntegral_comp_comm iA]
    have pp : Function.Periodic (fun t => B (z,t)) (2*Real.pi) := fun t => by simpa using pB (z,t)
    have heq (t : ℝ) : half (z,t) = (z,t+Real.pi) := by simp [half]
    have shiftInt : (∫ t in (0:ℝ)..2*Real.pi, B (half (z,t))) = ∫ t in (0:ℝ)..2*Real.pi, B (z,t) := by
      simp_rw [heq]
      change (∫ t in (0:ℝ)..2*Real.pi, (fun s => B (z,s)) (t+Real.pi)) = _
      rw [intervalIntegral.integral_comp_add_right (fun s => B (z,s)) Real.pi,zero_add,add_comm (2*Real.pi) Real.pi]
      simpa using pp.intervalIntegral_add_eq Real.pi 0
    have avg : (∫ t in (0:ℝ)..2*Real.pi, A (z,t)) = ∫ t in (0:ℝ)..2*Real.pi, B (z,t) := by
      unfold A
      have ib : IntervalIntegrable (fun t : ℝ => B (half (z,t))) volume 0 (2*Real.pi) :=
        (cont (B ∘ half) (sB.comp shalf)).intervalIntegrable _ _
      rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_add
        ((cont B sB).intervalIntegrable _ _) ib,shiftInt]
      ring
    rw [avg]
    simp only [B,future_eq,intervalIntegral.integral_neg,Wvalue,q,Complex.ofRealCLM_apply,Complex.real_smul,
      ofReal_neg,ofReal_mul]
    ring
  · intro z
    have even (w : Circle) : u z (w*Circle.exp Real.pi) = u z w := by
      let t := (w:ℂ).arg
      have rel : Circle.exp t = w := Circle.exp_arg _
      rw [← rel,← Circle.exp_add,liftAt,liftAt]
      simpa [half] using congrArg Complex.ofReal (aHalf (z,t))
    exact ⟨zero_for_odd u z even _ (Or.inr rfl),zero_for_odd u z even _ (Or.inl rfl)⟩

end
end TransportOkaGrauert.ScalarWPrimitive
