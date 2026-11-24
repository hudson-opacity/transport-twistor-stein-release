import TransportOkaGrauert.HyperbolicSimple
import TransportOkaGrauert.ManifoldStein

/-! A single nonflat model has all the geometric hypotheses and the complete
complex-manifold Stein conclusion, with the very same globally smooth factor. -/
namespace TransportOkaGrauert.HyperbolicCertificate
open Set Metric ChartStein ChartSteinAtlas HyperbolicSimple
open scoped Manifold

theorem simple_stein {c : ℝ} (hc : 0<c) (h1 : c<1) :
    SimpleDiskTarget.SimpleMetric (globalFactor c) ∧
    (∀ z ∈ closedBall (0:ℂ) 1, SimpleDiskTarget.curvature (globalFactor c) z = -4*c^2) ∧
    ∀ U : Set ℂ, ∀ hU : IsOpen U, U ⊆ ball 0 1 →
      ∃ A : HolomorphicCover (globalFactor c) U, letI := A.chartedSpace hU
        IsManifold 𝓘(ℂ, E) 1 (domain U) ∧ SteinCriterion.SteinConditions (domain U) := by
  refine ⟨simple hc h1,fun _ hz => curvature_globalFactor hc h1 (mem_closedBall_zero_iff.mp hz),?_⟩
  intro U openU subU
  apply ManifoldStein.exists_stein_manifold openU subU
  apply stein_congr openU _ (HyperbolicStein.poincare_disk hc h1 U openU subU)
  intro z hz
  exact (factor_agrees hc h1 ((mem_ball_zero_iff.mp (subU hz)).le.trans (one_lt_radius hc h1).le)).self_of_nhds.symm
end TransportOkaGrauert.HyperbolicCertificate
