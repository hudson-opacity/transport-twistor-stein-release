import TransportOkaGrauert.ScalarGeneralWTransfer

/-! # Cancellation of the polar density against the smooth angular weight -/
noncomputable section
namespace TransportOkaGrauert.ScalarGeneralKernel
open Metric Set SimpleDiskTarget
open scoped ContDiff

theorem density_spatialWeight_off {σ : ℂ → ℝ} (simple : SimpleMetric σ) {E : ℂ × ℂ → ℂ}
    (sE : ContDiff ℝ ∞ E) {a : ℂ} (ha : ‖a‖ < 1) (C : Coordinates σ a)
    (ce : C.endpoint = fun v => E (a,v)) (W : ℂ × ℂ → ℝ) (g : ℂ → ℝ)
    {y : ℂ} (hy : y ∈ ball (0:ℂ) 1) (hne : a ≠ y) :
    C.density y * spatialWeight C E W g y = Real.exp (2*σ y)*W (a,y)*g y := by
  have nx : C.logMap y ≠ 0 := by
    intro e
    have right := (C.right y hy).2
    rw [e,C.endpoint_zero] at right
    exact hne right
  have norm := norm_ne_zero_iff.mpr nx
  rw [← density_jacobian simple sE ha C ce hy]
  unfold Coordinates.density spatialWeight
  field_simp [norm]

/-- The spatial density becomes the intrinsic area factor, also at the centre when the
kernel vanishes on the diagonal of the input support. -/
theorem density_spatialWeight {σ : ℂ → ℝ} (simple : SimpleMetric σ) {E : ℂ × ℂ → ℂ}
    (sE : ContDiff ℝ ∞ E) {a : ℂ} (ha : ‖a‖ < 1) (C : Coordinates σ a)
    (ce : C.endpoint = fun v => E (a,v)) {W : ℂ × ℂ → ℝ} {g : ℂ → ℝ} {B : Set ℂ}
    (diag : a ∈ B → W (a,a) = 0) (off : ∀ z ∉ B, g z = 0)
    {y : ℂ} (hy : y ∈ ball (0:ℂ) 1) :
    C.density y * spatialWeight C E W g y = Real.exp (2*σ y)*W (a,y)*g y := by
  by_cases e : a = y
  · subst y
    by_cases h : a ∈ B
    · simp [spatialWeight,diag h]
    · simp [spatialWeight,off a h]
  · exact density_spatialWeight_off simple sE ha C ce W g hy e

end TransportOkaGrauert.ScalarGeneralKernel
