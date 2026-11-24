import TransportOkaGrauert.Descent
import TransportOkaGrauert.Gauge

namespace TransportOkaGrauert

/-- The reduction used in Theorem 4.13. The topology, allowed Fourier modes,
gauge subgroup, local solvability and geometric twistor presentation must be
supplied by a concrete surface theory. -/
theorem triviality_of_local_gauges
    {R B : Type*} [Ring R] (D : TransportOperator R) (U : Set R) (G : Subgroup Rˣ)
    [TopologicalSpace U] [PreconnectedSpace U] (hzero : (0 : R) ∈ U)
    (iso : Setoid B) (P : TwistorPresentation (D.orbitSetoid U G) iso)
    (product : B) (hproduct : iso.r (P.toBundle ⟨0, hzero⟩) product)
    (localGauge : ∀ a : U, ∃ V : Set U, IsOpen V ∧ a ∈ V ∧
      ∀ b ∈ V, ∃ f : G, D.gauge a.val f.val = b.val) :
    (∀ a : U, ∃ f : G, D.X (f.val : R) + a.val * (f.val : R) = 0) ∧
    ∀ b, iso.r b product := by
  let r := D.orbitSetoid U G
  have hopen := open_classes_of_local_reachability r localGauge
  exact ⟨D.integratingFactor_of_open_orbits U G hzero hopen,
    P.allBundlesTrivial ⟨0, hzero⟩ product hproduct
      (fun a => related_of_open_classes r hopen a _)⟩

end TransportOkaGrauert
