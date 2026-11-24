import TransportOkaGrauert.ScalarNormalBase
import TransportOkaGrauert.ScalarNormalKernel
import TransportOkaGrauert.ScalarGeneralMean

/-! # Invariant means separate compactly supported base densities -/
noncomputable section
namespace TransportOkaGrauert.ScalarRayPairing
open SimpleDiskTarget JacobiEnlargement GeodesicFlowExtension PathContinuation ScalarGeneralTransport
open ChartCoefficients Complex Set Metric MeasureTheory Filter
open scoped ContDiff Topology Interval

local instance : Fact (0 < 2*Real.pi) := ⟨Real.two_pi_pos⟩

theorem angularIntegral_smooth {h : AngleTrace} (hh : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ (angularIntegral h) := by
  let g := fun p : State => h (p.1,p.2-Real.pi)
  have sg : ContDiff ℝ ∞ g := hh.comp (contDiff_fst.prodMk (contDiff_snd.sub contDiff_const))
  have s := ScalarGeneralCauchy.integral_smooth sg Real.two_pi_pos
  convert s using 1
  funext z
  have eq := intervalIntegral.integral_comp_add_right (fun t => h (z,t)) (-Real.pi) (a:=0) (b:=2*Real.pi)
  simpa [angularIntegral,g,sub_eq_add_neg,show 2*Real.pi + -Real.pi = Real.pi by ring] using eq.symm

theorem invariant_trace_of_angular {σ : ℂ → ℝ} {A : AngleTrace} (hA : ContDiff ℝ ∞ A) (pA : period A)
    (X : ∀ p : State, ‖p.1‖ ≤ 1 → fderiv ℝ A p (chartVector σ p) = 0) :
    ∃ h : Trace, ContDiff ℝ ∞ (lifted h) ∧
      (∀ z ∈ closedBall (0:ℂ) 1, ∀ w, Isothermal.geodesicX σ h z w = 0) ∧
      ∀ z : ℂ, coefficient h 0 z = ((angularIntegral A z / (2*Real.pi) : ℝ) : ℂ) := by
  let h : Trace := fun z w => A (z,(w:ℂ).arg)
  have eq (z : ℂ) (t : ℝ) : h z (Circle.exp t) = (A (z,t) : ℂ) := by
    have e := Circle.exp_arg (Circle.exp t)
    obtain ⟨m,hm⟩ := Circle.exp_eq_exp.mp e
    have per : Function.Periodic (fun t => A (z,t)) (2*Real.pi) := fun a => by
      simpa [Prod.mk_add_mk] using pA (z,a)
    change (A (z,(Circle.exp t : ℂ).arg) : ℂ) = _
    rw [hm]
    exact congrArg Complex.ofReal (per.int_mul m t)
  have lift : lifted h = Complex.ofRealCLM ∘ A := funext (fun p => eq p.1 p.2)
  have sh : ContDiff ℝ ∞ (lifted h) := lift ▸ ofRealCLM.contDiff.comp hA
  refine ⟨h,sh,?_,?_⟩
  · intro z hz w
    let θ := (w:ℂ).arg
    have e := Circle.exp_arg w
    change Circle.exp θ = w at e
    rw [← e,geodesicX_eq_chart_derivative _ _ _ θ (sh.differentiable (by simp) (z,θ))]
    change fderiv ℝ (lifted h) (z,θ) _ = 0
    rw [lift,fderiv_comp _ ofRealCLM.differentiableAt (hA.differentiable (by simp) _),
      ContinuousLinearMap.fderiv,ContinuousLinearMap.comp_apply,X _ (mem_closedBall_zero_iff.mp hz),map_zero]
  · intro z
    rw [coefficient,fourierCoeff_eq_intervalIntegral _ _ (-Real.pi),show -Real.pi+2*Real.pi = Real.pi by ring]
    simp only [neg_zero,fourier_zero,one_smul,ChartModes.toCircle_angle,eq]
    have ct : Continuous (fun t : ℝ => A (z,t)) := hA.continuous.comp (continuous_const.prodMk continuous_id)
    have op := ofRealCLM.intervalIntegral_comp_comm (μ := volume) (ct.intervalIntegrable (-Real.pi) Real.pi)
    change _ • (∫ t in -Real.pi..Real.pi, ofRealCLM (A (z,t))) = _
    rw [op]
    simp [angularIntegral,Complex.real_smul,div_eq_mul_inv,mul_comm]

/-- Every nonzero smooth real density supported in the closed radius-`r`
disk has a strictly positive Euclidean area pairing with the normalized
zeroth coefficient of a smooth invariant trace. The test is smoothly cut
off inside the outer disk and agrees with the trace mean throughout the
smaller disk. -/
theorem separates_on_subdisk {σ : ℂ → ℝ} (simple : SimpleMetric σ) {r : ℝ}
    (hr : 0 < r) (hr₁ : r < 1) {c : ℂ → ℝ} (hc : ContDiff ℝ ∞ c)
    (off : ∀ z, r < ‖z‖ → c z = 0) (ne : c ≠ 0) :
    ∃ a : ℂ → ℝ, ContDiff ℝ ∞ a ∧ tsupport a ⊆ ball (0:ℂ) 1 ∧
      (∃ h : Trace, ContDiff ℝ ∞ (lifted h) ∧
        (∀ z ∈ closedBall (0:ℂ) 1, ∀ w, Isothermal.geodesicX σ h z w = 0) ∧
        ∀ z ∈ ball (0:ℂ) r, coefficient h 0 z = (a z : ℂ)) ∧
      0 < ∫ z in ball (0:ℂ) 1, c z * a z := by
  obtain ⟨F⟩ := JacobiEnlargement.exists_flow simple
  obtain ⟨W⟩ := exists_window F simple
  let f := fun z => Real.exp (-(2*σ z)) * c z
  have hf : ContDiff ℝ ∞ f := (((contDiff_const.mul simple.smooth).neg).exp).mul hc
  have zf (z : ℂ) (hz : r < ‖z‖) : f z = 0 := by simp [f,off z hz]
  let g := fun p : State => f p.1
  let A := full F W g
  have hg : ContDiff ℝ ∞ g := hf.comp contDiff_fst
  have pg : period g := fun p => by simp [g]
  have zg : supported g := fun p h => zf p.1 (hr₁.trans h)
  have sa := full_smooth F W hg
  have pa := full_period F W pg
  have xa (p : State) (hp : ‖p.1‖ ≤ 1) : fderiv ℝ A p (chartVector σ p) = 0 := by
    have e := F.germ hp
    have field : chartVector σ p = chartVector F.factor p := by
      simp [chartVector,Isothermal.angularDrift,e.eq_of_nhds,e.fderiv_eq]
    rw [field]
    change fderiv ℝ (past F W g + future F W g) p _ = _
    rw [fderiv_add ((past_smooth F W hg).differentiable (by simp) p)
      ((future_smooth F W hg).differentiable (by simp) p),ContinuousLinearMap.add_apply]
    have d := window_derivatives F W hg zg p hp
    exact (congrArg₂ (·+·) d.1 d.2).trans (add_neg_cancel _)
  obtain ⟨h,sh,xh,ch⟩ := invariant_trace_of_angular sa pa xa
  obtain ⟨w,_,_,_,nw,_,sq⟩ := energy_square F W hr.le hr₁
  have pos : 0 < integral F (fun p => f p.1 * A p) := by
    have en := sq g hg pg (fun p => zf p.1)
    have ge : 0 ≤ integral F (fun p => f p.1 * A p) := by
      rw [show integral F (fun p => f p.1 * A p) = _ from en]
      apply integral_nonneg
      intro x
      exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (nw _) (sq_nonneg _))
    refine lt_of_le_of_ne ge ?_
    intro ez
    have hzero := zero_energy_injective F simple W hr.le hr₁ hf zf ez.symm
    apply ne
    funext z
    have cz := congrFun hzero z
    exact (mul_eq_zero.mp cz).resolve_left (Real.exp_pos _).ne'
  have base := integral_on_base F hf.continuous (fun z h => zf z (hr₁.trans h)) sa.continuous
  have cancel (z : ℂ) : Real.exp (2*σ z) * f z = c z := by simp [f,← mul_assoc,← Real.exp_add]
  have basepos : 0 < ∫ z : ℂ, c z * angularIntegral A z := by
    change integral F (fun p => f p.1 * A p) = ∫ z : ℂ, Real.exp (2*σ z) * f z * angularIntegral A z at base
    rw [base] at pos
    simpa only [cancel] using pos
  let R := (r+1)/2
  let β : ContDiffBump (0:ℂ) := ⟨(r+R)/2,R,by dsimp [R]; linarith,by dsimp [R]; linarith⟩
  let a := fun z => β z * (angularIntegral A z / (2*Real.pi))
  have smooth : ContDiff ℝ ∞ a := β.contDiff.mul ((angularIntegral_smooth sa).div_const _)
  have one (z : ℂ) (hz : ‖z‖ ≤ r) : β z = 1 :=
    β.one_of_mem_closedBall (by simp only [mem_closedBall,dist_zero_right]; change ‖z‖ ≤ (r+R)/2; dsimp [R]; linarith)
  have az (z : ℂ) (hz : R ≤ ‖z‖) : a z = 0 := by
    have e := β.zero_of_le_dist (x := z) (by simpa [β] using hz)
    simp [a,e]
  have supp : tsupport a ⊆ closedBall (0:ℂ) R := by
    apply closure_minimal _ isClosed_closedBall
    intro z hz
    by_contra! eo
    exact hz (az z (by simpa using le_of_lt (by simpa using eo : R < ‖z‖)))
  refine ⟨a,smooth,supp.trans (closedBall_subset_ball (by dsimp [R]; linarith)),⟨h,sh,xh,?_⟩,?_⟩
  · intro z hz
    rw [ch]; simp [a,A,one z (mem_ball_zero_iff.mp hz).le]
  · have data (z : ℂ) : c z * a z = (2*Real.pi)⁻¹ * (c z * angularIntegral A z) := by
      by_cases hz : ‖z‖ ≤ r
      · simp [a,one z hz,div_eq_mul_inv]; ring
      · simp [off z (lt_of_not_ge hz)]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by
      change c z * a z = 0; rw [off z (by simpa using hr₁.trans_le (by simpa using hz : 1 ≤ ‖z‖)),zero_mul])]
    simp only [data,integral_const_mul]
    exact mul_pos (inv_pos.mpr Real.two_pi_pos) basepos

/-- A smooth real density on the outer disk annihilating every extendible
inner invariant mean vanishes identically. The base integral is ordinary
Euclidean area. -/
theorem annihilator_eq_zero {σ : ℂ → ℝ} (simple : SimpleMetric σ) {r : ℝ}
    (hr : 0 < r) (hr₁ : r < 1) {c : ℂ → ℝ} (hc : ContDiff ℝ ∞ c)
    (off : ∀ z, r < ‖z‖ → c z = 0)
    (orthogonal : ∀ a : ℂ → ℝ, ContDiff ℝ ∞ a → tsupport a ⊆ ball (0:ℂ) 1 →
      (∃ h : Trace, ContDiff ℝ ∞ (lifted h) ∧
        (∀ z ∈ ball (0:ℂ) r, ∀ w, Isothermal.geodesicX σ h z w = 0) ∧
        ∀ z ∈ ball (0:ℂ) r, coefficient h 0 z = (a z : ℂ)) →
      (∫ z in ball (0:ℂ) 1, c z * a z) = 0) : c = 0 := by
  by_contra n
  obtain ⟨a,sa,supp,⟨h,sh,xh,mean⟩,pos⟩ := separates_on_subdisk simple hr hr₁ hc off n
  have eq := orthogonal a sa supp ⟨h,sh,fun z hz => xh z (mem_closedBall_zero_iff.mpr
    ((mem_ball_zero_iff.mp hz).trans hr₁).le),mean⟩
  exact pos.ne' eq

end TransportOkaGrauert.ScalarRayPairing
