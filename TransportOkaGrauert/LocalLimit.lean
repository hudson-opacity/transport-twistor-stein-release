import TransportOkaGrauert.Reduction
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! An alternative quantitative interface for the open-orbit step. One may
supply a convergent inverse iteration instead of a local solvability theorem.
The estimates needed to produce such a sequence on a surface are external. -/
namespace TransportOkaGrauert

open Filter Topology

/-- Summable corrections in a complete metric on gauges yield an exact
solution when the residual tends to the target in a Hausdorff space. -/
theorem solve_of_summable_steps {G Y : Type*} [PseudoMetricSpace G] [CompleteSpace G]
    [TopologicalSpace Y] [T2Space Y] {action : G → Y} (hc : Continuous action)
    (target : Y) (u : ℕ → G) (bounds : ℕ → ℝ)
    (hb : Summable bounds) (hstep : ∀ k, dist (u k) (u (k+1)) ≤ bounds k)
    (residual : Tendsto (fun k => action (u k)) atTop (𝓝 target)) :
    ∃ f, action f = target := by
  obtain ⟨f, h⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_dist_le_of_summable bounds hstep hb)
  exact ⟨f, tendsto_nhds_unique (hc.continuousAt.tendsto.comp h) residual⟩

/-- The local iteration only has to handle targets in a neighborhood of its
base attenuation. Connectedness then supplies the global result. -/
theorem triviality_of_approximate_gauges
    {R B : Type*} [Ring R] [TopologicalSpace R] [T2Space R]
    (D : TransportOperator R) (U : Set R) (G : Subgroup Rˣ)
    [metricG : PseudoMetricSpace G] [@CompleteSpace G metricG.toUniformSpace] [PreconnectedSpace U] (hzero : (0 : R) ∈ U)
    (iso : Setoid B) (P : TwistorPresentation (D.orbitSetoid U G) iso)
    (product : B) (hproduct : iso.r (P.toBundle ⟨0, hzero⟩) product)
    (hc : ∀ a : U, @Continuous G R metricG.toUniformSpace.toTopologicalSpace _
      (fun f : G => D.gauge a.val f.val))
    (iterate : ∀ a : U, ∃ V : Set U, IsOpen V ∧ a ∈ V ∧ ∀ b ∈ V,
      ∃ (u : ℕ → G) (d : ℕ → ℝ), Summable d ∧
        (∀ k, dist (u k) (u (k+1)) ≤ d k) ∧
        Tendsto (fun k => D.gauge a.val (u k).val) atTop (𝓝 b.val)) :
    (∀ a : U, ∃ f : G, D.X (f.val : R) + a.val * (f.val : R) = 0) ∧
      ∀ b, iso.r b product := by
  apply triviality_of_local_gauges D U G hzero iso P product hproduct
  intro a
  obtain ⟨V, hopen, ha, h⟩ := iterate a
  refine ⟨V, hopen, ha, fun b hb => ?_⟩
  obtain ⟨u, d, hd, hstep, hr⟩ := h b hb
  exact solve_of_summable_steps (hc a) b.val u d hd hstep hr

end TransportOkaGrauert
