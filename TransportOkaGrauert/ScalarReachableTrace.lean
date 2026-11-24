import TransportOkaGrauert.ScalarInvariantSeparation
import TransportOkaGrauert.SteinMomentBridge

/-! # Linear combinations of smooth invariant means -/
noncomputable section
namespace TransportOkaGrauert.ScalarReachableTrace
open Complex SimpleDiskTarget Set Metric MeasureTheory Filter PathContinuation FrameLevi
open ScalarGeneralTransport ScalarGeneralReduction ChartCoefficients
open scoped ContDiff Topology

local instance : Fact (0 < 2*Real.pi) := ⟨Real.two_pi_pos⟩

def Reachable (σ : ℂ → ℝ) (r : ℝ) (a : ℂ → ℂ) : Prop :=
  ∃ h : Trace, ContDiff ℝ ∞ (lifted h) ∧
    (∀ z ∈ ball (0:ℂ) r, ∀ w, Isothermal.geodesicX σ h z w = 0) ∧
    ∀ z ∈ ball (0:ℂ) r, coefficient h 0 z = a z

theorem congr {σ r a b} (ha : Reachable σ r a) (eq : EqOn a b (ball (0:ℂ) r)) :
    Reachable σ r b := by
  obtain ⟨h,sh,inv,mean⟩ := ha
  exact ⟨h,sh,inv,fun z hz => (mean z hz).trans (eq hz)⟩

theorem zero (σ : ℂ → ℝ) (r : ℝ) : Reachable σ r 0 := by
  refine ⟨fun _ _ => 0,contDiff_const,?_,?_⟩
  · intro z _ w
    let θ := (w:ℂ).arg
    rw [← Circle.exp_arg w,geodesicX_eq_chart_derivative _ _ _ _ (differentiableAt_const _)]
    simp
  · intro z _; simp [coefficient,fourierCoeff]

theorem lincomb {σ r a b} (ha : Reachable σ r a) (hb : Reachable σ r b) (u v : ℂ) :
    Reachable σ r (fun z => u*a z+v*b z) := by
  obtain ⟨h,sh,xh,eh⟩ := ha
  obtain ⟨k,sk,xk,ek⟩ := hb
  let l : Trace := fun z w => u*h z w + v*k z w
  have sl : ContDiff ℝ ∞ (lifted l) := (contDiff_const.mul sh).add (contDiff_const.mul sk)
  refine ⟨l,sl,?_,?_⟩
  · intro z hz w
    let p : GeodesicFlowExtension.State := (z,(w:ℂ).arg)
    let θ := p.2
    have e : Circle.exp θ = w := Circle.exp_arg w
    have d (h : Trace) (s : ContDiff ℝ ∞ (lifted h)) :
        Isothermal.geodesicX σ h z w = fderiv ℝ (lifted h) p (chartVector σ p) := by
      rw [← e]
      exact geodesicX_eq_chart_derivative _ _ _ θ (s.differentiable (by simp) p)
    have a₁ := (d h sh).symm.trans (xh z hz w)
    have a₂ := (d k sk).symm.trans (xk z hz w)
    rw [d l sl]
    have dh := (sh.differentiable (by simp) p).hasFDerivAt
    have dk := (sk.differentiable (by simp) p).hasFDerivAt
    rw [show fderiv ℝ (lifted l) p = _ from ((dh.const_mul u).add (dk.const_mul v)).fderiv]
    simp [a₁,a₂]
  · intro z hz
    have ci (h : Trace) (s : ContDiff ℝ ∞ (lifted h)) (c : ℂ) :
        Integrable (fun t : DiskSeries.Angle => c*h z t.toCircle) AddCircle.haarAddCircle :=
      (continuous_const.mul (circle_cont s z)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have eq : coefficient l 0 z = u*coefficient h 0 z+v*coefficient k 0 z := by
      change fourierCoeff ((fun t : DiskSeries.Angle => u*h z t.toCircle) +
        (fun t : DiskSeries.Angle => v*k z t.toCircle)) 0 = _
      rw [fourierCoeff.add (ci h sh u) (ci k sk v),Pi.add_apply,fourierCoeff.const_mul (fun t : DiskSeries.Angle => h z t.toCircle),fourierCoeff.const_mul (fun t : DiskSeries.Angle => k z t.toCircle)]
      rfl
    rw [eq,eh z hz,ek z hz]

theorem complex_of_real {σ r} (realize : ∀ a : ℂ → ℝ, ContDiff ℝ ∞ a →
    Reachable σ r (fun z => (a z : ℂ))) (a : ℂ → ℂ) (ha : ContDiff ℝ ∞ a) : Reachable σ r a := by
  have e := lincomb (realize _ (Complex.reCLM.contDiff.comp ha)) (realize _ (Complex.imCLM.contDiff.comp ha)) 1 I
  apply congr e
  intro z _
  simp only [Function.comp_apply,reCLM_apply,imCLM_apply,one_mul]
  rw [mul_comm I,Complex.re_add_im]

end TransportOkaGrauert.ScalarReachableTrace
