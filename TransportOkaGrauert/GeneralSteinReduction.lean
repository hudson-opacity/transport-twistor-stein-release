import TransportOkaGrauert.PencilGeometry

/-! # The two outstanding inputs to the universal fixed-chart Stein theorem -/
namespace TransportOkaGrauert.GeneralSteinReduction
open ChartStein PencilLifts PencilGeometry SimpleDiskTarget

/-- For a given simple disk the raw pencil sources, boundary incidence, local
coordinates, separation and hull compactness are all conclusions once these
two inputs are supplied. No dependence on the centre is required of the chosen
scalar solution. -/
theorem for_metric {σ : ℂ → ℝ} (simple : SimpleMetric σ) (solve : ScalarSolvability σ)
    (radial : ∀ a : ClosedDisk, Nonempty (Data σ a)) (U : Set ℂ)
    (openU : IsOpen U) (subU : U ⊆ disk) : HasSteinProperties σ U :=
  ChartPencils.stein_for_simple_disk simple solve
    (fun a => toRaw simple.smooth (Classical.choice (radial a))) U openU subU

/-- This is a conditional reduction. The scalar theorem and the radial-geodesic
construction must both be proved uniformly for the universal check to pass. -/
theorem of_scalar_and_geometry
    (analytic : ∀ σ : ℂ → ℝ, SimpleMetric σ → ScalarSolvability σ)
    (geometric : ∀ σ : ℂ → ℝ, SimpleMetric σ → ∀ a : ClosedDisk, Nonempty (Data σ a)) :
    GeneralSimpleSurfaceStatement :=
  fun σ simple => for_metric simple (analytic σ simple) (geometric σ simple)
end TransportOkaGrauert.GeneralSteinReduction
