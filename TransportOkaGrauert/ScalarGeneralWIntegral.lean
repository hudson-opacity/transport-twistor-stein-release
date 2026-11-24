import TransportOkaGrauert.ScalarGeneralWAngular
import TransportOkaGrauert.ScalarWPrimitive

/-! # Radial and angular integration of the smooth W kernel -/

noncomputable section
namespace TransportOkaGrauert.ScalarGeneralKernel
open Metric Set MeasureTheory Filter SimpleDiskTarget JacobiEnlargement ScalarNormalLift
open scoped ContDiff Topology Interval

/-- Integrated polar angular integration by parts. The endpoint at radius zero
is harmless because the radial interval integral only uses positive radii. -/
theorem integrate_angular_test (u v : ℝ × ℝ → ℝ) (su : Continuous u) (sv : Continuous v)
    {b h : ℂ → ℝ} (sb : ContDiff ℝ ∞ b) (sh : ContDiff ℝ ∞ h)
    (eq : ∀ θ r : ℝ, 0 < r →
      r*u (θ,r) = b (turn r θ)*angularD h (turn r θ) ∧
      r*v (θ,r) = -(angularD b (turn r θ))*h (turn r θ)) {T : ℝ} (hT : 0 < T) :
    (∫ θ in (0:ℝ)..2*Real.pi, ∫ r in (0:ℝ)..T, u (θ,r)) =
       ∫ θ in (0:ℝ)..2*Real.pi, ∫ r in (0:ℝ)..T, v (θ,r) := by
  rw [rectangle_swap u su hT,rectangle_swap v sv hT,
    intervalIntegral.integral_of_le hT.le,intervalIntegral.integral_of_le hT.le]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro r hr
  apply mul_left_cancel₀ hr.1.ne'
  rw [← intervalIntegral.integral_const_mul,← intervalIntegral.integral_const_mul]
  calc
    _ = ∫ θ in (0:ℝ)..2*Real.pi, b (turn r θ)*angularD h (turn r θ) :=
      intervalIntegral.integral_congr (fun θ _ => (eq θ r hr.1).1)
    _ = _ := angular_parts r sb sh
    _ = _ := intervalIntegral.integral_congr (fun θ _ => (eq θ r hr.1).2.symm)

end TransportOkaGrauert.ScalarGeneralKernel
