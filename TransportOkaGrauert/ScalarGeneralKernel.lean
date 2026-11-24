import TransportOkaGrauert.SimpleRadialSpray
import Mathlib.Analysis.SpecialFunctions.PolarCoord

/-! # The kernel of the angular geodesic ray average

Angular measure is (dθ) and the radial variable is positive unit-speed
geodesic time. The physical base measure is Euclidean area in the conformal
chart. -/

noncomputable section
namespace TransportOkaGrauert.ScalarGeneralKernel

open Complex Set Metric MeasureTheory Filter ConformalFrame SimpleRadialVariation
open scoped ContDiff Topology

structure Coordinates (σ : ℂ → ℝ) (a : ℂ) where
  endpoint : ℂ → ℂ
  flow : ℝ × ℝ → Chart
  logMap : ℂ → ℂ
  endpoint_smooth : ContDiff ℝ ∞ endpoint
  flow_smooth : ContDiff ℝ ∞ flow
  log_smooth : ContDiffOn ℝ ∞ logMap (ball (0 : ℂ) 1)
  endpoint_zero : endpoint 0 = a
  right : ∀ y ∈ ball (0 : ℂ) 1, logMap y ∈ SimpleRadialStar.retained endpoint 1 ∧ endpoint (logMap y) = y
  left : ∀ x ∈ SimpleRadialStar.retained endpoint 1, endpoint x ∈ ball (0 : ℂ) 1 → logMap (endpoint x) = x
  initial : ∀ α : ℝ, flow (α,0) = (a,α,0)
  polar : ∀ α t : ℝ, (flow (α,t)).1 = endpoint (t • (Circle.exp α : ℂ))
  ode : ∀ q : ℝ × ℝ, ‖(flow q).1‖ ≤ 1 → (fun u => fderiv ℝ flow u (0,1)) =ᶠ[𝓝 q] X σ ∘ flow

theorem exists_coordinates {σ : ℂ → ℝ} (simple : SimpleDiskTarget.SimpleMetric σ)
    {a : ℂ} (ha : ‖a‖ < 1) : Nonempty (Coordinates σ a) := by
  obtain ⟨f,δ,F,L,sf,_,sF,sL,cen,right,left,ini,pol,ode⟩ := SimpleRadialSpray.normal_coordinates simple ha
  exact ⟨⟨f,F,L,sf,sF,sL,cen,right,left,ini,fun α t => (pol α t).1,ode⟩⟩

namespace Coordinates
variable {σ : ℂ → ℝ} {a : ℂ} (C : Coordinates σ a)

def velocities : Set ℂ := SimpleRadialStar.retained C.endpoint 1 ∩ C.endpoint ⁻¹' ball (0 : ℂ) 1

theorem measurable_velocities : MeasurableSet C.velocities :=
  (SimpleRadialStar.isClosed_retained C.endpoint_smooth.continuous 1).measurableSet.inter
    (isOpen_ball.preimage C.endpoint_smooth.continuous).measurableSet

theorem log_image : C.logMap '' ball (0 : ℂ) 1 = C.velocities := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact ⟨(C.right y hy).1, show C.endpoint (C.logMap y) ∈ ball (0:ℂ) 1 by rwa [(C.right y hy).2]⟩
  · intro hx
    exact ⟨C.endpoint x,hx.2,C.left x hx.1 hx.2⟩

theorem log_injective : InjOn C.logMap (ball (0 : ℂ) 1) := by
  intro y hy z hz eq
  rw [← (C.right y hy).2, eq, (C.right z hz).2]

def rayAverage (g : ℂ → ℂ) : ℂ :=
  ∫ p : ℝ × ℝ in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
    C.velocities.indicator (fun x => g (C.endpoint x)) (p.1 • (Circle.exp p.2 : ℂ))

def density (y : ℂ) : ℝ := |(fderiv ℝ C.logMap y).det| / ‖C.logMap y‖

/-- The actual change of variables, with the simple metric's globally invertible
first-exit exponential map. The single point at the polar origin has zero area. -/
theorem rayAverage_eq_area (g : ℂ → ℂ) :
    C.rayAverage g = ∫ y in ball (0 : ℂ) 1, C.density y • g y := by
  classical
  let h (x : ℂ) := ‖x‖⁻¹ • g (C.endpoint x)
  have polar (p : ℝ × ℝ) : Complex.polarCoord.symm p = p.1 • (Circle.exp p.2 : ℂ) := by
    simp [Complex.real_smul, Circle.coe_exp, Complex.exp_mul_I, mul_add]
  have first : C.rayAverage g =
      ∫ p in polarCoord.target, p.1 • C.velocities.indicator h (Complex.polarCoord.symm p) := by
    apply setIntegral_congr_fun polarCoord.open_target.measurableSet
    intro p hp
    change 0 < p.1 ∧ _ at hp
    dsimp only
    rw [← polar p]
    by_cases inside : Complex.polarCoord.symm p ∈ C.velocities
    · simp only [Set.indicator_of_mem inside,h,Complex.norm_polarCoord_symm,abs_of_pos hp.1,
        smul_smul,mul_inv_cancel₀ hp.1.ne',one_smul]
    · simp only [Set.indicator_of_notMem inside,smul_zero]
  rw [first, Complex.integral_comp_polarCoord_symm, integral_indicator C.measurable_velocities,
    ← C.log_image, integral_image_eq_integral_abs_det_fderiv_smul volume isOpen_ball.measurableSet
      (f' := fderiv ℝ C.logMap) (fun y hy => (((C.log_smooth y hy).contDiffAt
        (isOpen_ball.mem_nhds hy)).differentiableAt (by simp)).hasFDerivAt.hasFDerivWithinAt) C.log_injective]
  apply setIntegral_congr_fun isOpen_ball.measurableSet
  intro y hy
  simp only [h, (C.right y hy).2, density, div_eq_mul_inv, smul_smul]

theorem log_zero (ha : ‖a‖ < 1) : C.logMap a = 0 := by
  have h0 : (0 : ℂ) ∈ SimpleRadialStar.retained C.endpoint 1 := fun t _ => by simp [C.endpoint_zero, ha.le]
  simpa only [C.endpoint_zero] using C.left 0 h0 (by simpa [C.endpoint_zero] using ha)

theorem endpoint_derivative (ha : ‖a‖ < 1) : fderiv ℝ C.endpoint 0 =
    Real.exp (-σ a) • ContinuousLinearMap.id ℝ ℂ := by
  have radial (α : ℝ) : fderiv ℝ C.endpoint 0 (Circle.exp α : ℂ) = Real.exp (-σ a) • (Circle.exp α : ℂ) := by
    have ode0 := (C.ode (α,0) (by simp [C.initial,ha.le])).self_of_nhds
    have line := (C.flow_smooth.differentiable (by simp) (α,0)).hasFDerivAt.comp_hasDerivAt 0
      ((hasDerivAt_const (0:ℝ) α).prodMk (hasDerivAt_id (0:ℝ)))
    have h : HasDerivAt (fun s => C.flow (α,s)) (X σ (C.flow (α,0))) 0 := by
      change fderiv ℝ C.flow (α,0) (0,1) = X σ (C.flow (α,0)) at ode0
      rw [← ode0]
      exact line
    have base := (ContinuousLinearMap.fst ℝ ℂ (ℝ × ℝ)).hasFDerivAt.comp_hasDerivAt 0 h
    have actual := (C.endpoint_smooth.differentiable (by simp) ((0:ℝ) • (Circle.exp α : ℂ))).hasFDerivAt.comp_hasDerivAt
      0 ((hasDerivAt_id (0:ℝ)).smul_const (Circle.exp α : ℂ))
    have same := actual.unique (base.congr_of_eventuallyEq (.of_forall (fun s => (C.polar α s).symm)))
    change fderiv ℝ C.endpoint ((0:ℝ) • (Circle.exp α : ℂ)) ((1:ℝ) • (Circle.exp α : ℂ)) =
      (X σ (C.flow (α,0))).1 at same
    rw [(chart_columns σ (C.flow (α,0))).1, C.initial] at same
    simpa only [zero_smul,one_smul,Complex.real_smul] using same
  ext x
  change fderiv ℝ C.endpoint 0 x = Real.exp (-σ a) • x
  conv_lhs => arg 2; rw [← polar_angle x]
  rw [map_smul,radial,smul_comm,polar_angle]

theorem log_derivative (ha : ‖a‖ < 1) : fderiv ℝ C.logMap a =
    Real.exp (σ a) • ContinuousLinearMap.id ℝ ℂ := by
  have ha' : a ∈ ball (0:ℂ) 1 := mem_ball_zero_iff.mpr ha
  have hd := ((C.log_smooth a ha').contDiffAt (isOpen_ball.mem_nhds ha')).differentiableAt (by simp)
  have d := ((C.endpoint_smooth.differentiable (by simp)) (C.logMap a)).hasFDerivAt.comp a hd.hasFDerivAt
  have h : C.endpoint ∘ C.logMap =ᶠ[𝓝 a] id := by
    filter_upwards [isOpen_ball.mem_nhds ha'] with y hy using (C.right y hy).2
  have E := d.unique ((hasFDerivAt_id a).congr_of_eventuallyEq h)
  rw [C.log_zero ha, C.endpoint_derivative ha] at E
  ext x
  have Ex := DFunLike.congr_fun E x
  change Real.exp (-σ a) • (fderiv ℝ C.logMap a x) = x at Ex
  change fderiv ℝ C.logMap a x = Real.exp (σ a) • x
  calc
    _ = Real.exp (σ a) • (Real.exp (-σ a) • (fderiv ℝ C.logMap a x)) := by
      rw [smul_smul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_smul]
    _ = _ := by rw [Ex]

private theorem det_scalar (c : ℝ) : (c • ContinuousLinearMap.id ℝ ℂ).det = c ^ 2 := by
  change LinearMap.det (c • (LinearMap.id : ℂ →ₗ[ℝ] ℂ)) = _
  rw [LinearMap.det_smul, Complex.finrank_real_complex, LinearMap.det_id, mul_one]

/-- The leading coefficient of the physical kernel is isotropic, including along
arbitrary sequences approaching the pole. -/
theorem diagonal (ha : ‖a‖ < 1) :
    Tendsto (fun y => ‖y-a‖ * C.density y) (𝓝[≠] a) (𝓝 (Real.exp (σ a))) := by
  let c := Real.exp (σ a)
  have hc : 0 < c := Real.exp_pos _
  have ha' : a ∈ ball (0:ℂ) 1 := mem_ball_zero_iff.mpr ha
  have sm := (C.log_smooth a ha').contDiffAt (isOpen_ball.mem_nhds ha')
  have hd := (sm.differentiableAt (by simp)).hasFDerivAt
  rw [C.log_derivative ha] at hd
  have err := (hasFDerivAt_iff_tendsto.mp hd).mono_left (nhdsWithin_le_nhds (s := ({a}ᶜ : Set ℂ)))
  have ratio : Tendsto (fun y => ‖C.logMap y‖ / ‖y-a‖) (𝓝[≠] a) (𝓝 c) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [err.eventually (Iio_mem_nhds hε), self_mem_nhdsWithin] with y e ne
    have hy : 0 < ‖y-a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr ne)
    change ‖y-a‖⁻¹ * ‖C.logMap y - C.logMap a - c • (y-a)‖ < ε at e
    rw [C.log_zero ha, sub_zero, inv_mul_eq_div] at e
    have bound := abs_norm_sub_norm_le (C.logMap y) (c • (y-a))
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc] at bound
    rw [Real.dist_eq, div_sub' hy.ne', abs_div, abs_of_pos hy]
    apply lt_of_le_of_lt _ e
    exact div_le_div_of_nonneg_right (by simpa [mul_comm] using bound) hy.le
  have cdet : ContinuousAt (fun y => (fderiv ℝ C.logMap y).det) a :=
    ContinuousLinearMap.continuous_det.continuousAt.comp (sm.fderiv_right (m := ∞) (by simp)).continuousAt
  have detlim := cdet.abs.tendsto.mono_left (nhdsWithin_le_nhds (s := ({a}ᶜ : Set ℂ)))
  rw [C.log_derivative ha, det_scalar, abs_of_nonneg (sq_nonneg _)] at detlim
  have quotient := detlim.div ratio hc.ne'
  have value : c ^ 2 / c = c := by field_simp
  change Tendsto _ _ (𝓝 c)
  rw [← value]
  refine quotient.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  change |(fderiv ℝ C.logMap y).det| / (‖C.logMap y‖ / ‖y-a‖) = ‖y-a‖ * C.density y
  rw [density, div_div_eq_mul_div]
  ring

end Coordinates
end TransportOkaGrauert.ScalarGeneralKernel
