import TransportOkaGrauert.ScalarPestovEstimate

/-! # Complex scalar X-ray injectivity on a simple conformal disk -/
noncomputable section
namespace TransportOkaGrauert.ScalarPestov
open SimpleDiskTarget Complex ScalarRayPrimitive MeasureTheory Set
open scoped ContDiff Interval

theorem boundary_ray_injective_complex {σ : ℂ → ℝ} (simple : SimpleMetric σ) {f : ℂ → ℂ}
    (hf : ContDiff ℝ ∞ f) (off : ∀ z, 1 < ‖z‖ → f z = 0)
    (null : ∀ (a b : ℝ), a < b → ∀ z θ, unitGeodesicOn σ z θ (Icc a b) →
      (∀ t ∈ Icc a b, ‖z t‖ ≤ 1) → ‖z a‖ = 1 → ‖z b‖ = 1 → (∫ t in a..b, f (z t)) = 0) :
    f = 0 := by
  have eq (L : ℂ →L[ℝ] ℝ) : (fun x => L (f x)) = 0 := by
    apply boundary_ray_injective simple (L.contDiff.comp hf) (fun x hx => by change L (f x) = 0; rw [off x hx,map_zero])
    intro a b hab z θ geo disk ha hb
    have ct : ContinuousOn (fun t => f (z t)) (Icc a b) := hf.continuous.comp_continuousOn
      (fun t ht => (geo t ht).1.continuousWithinAt)
    have it : IntervalIntegrable (fun t => f (z t)) volume a b := (uIcc_of_le hab.le ▸ ct).intervalIntegrable
    exact (L.intervalIntegral_comp_comm it).trans (by rw [null a b hab z θ geo disk ha hb,map_zero])
  funext x
  exact Complex.ext (congrFun (eq reCLM) x) (congrFun (eq imCLM) x)

end TransportOkaGrauert.ScalarPestov
