import TransportOkaGrauert.SimpleMetricGerm
import TransportOkaGrauert.GeneralStein

/-! # Stein properties for a smooth metric germ on the closed disk -/
noncomputable section
namespace TransportOkaGrauert.GeneralStein
open ChartStein SimpleDiskTarget Set Metric Filter Manifold
open scoped ContDiff Topology

/-- Transport holomorphicity only uses the metric germ at the base point. -/
private theorem holOn_iff_of_germs {σ τ : ℂ → ℝ} {U : Set ℂ} {f : E → ℂ}
    (eq : ∀ z ∈ U, τ =ᶠ[𝓝 z] σ) : HolOn τ U f ↔ HolOn σ U f := by
  apply forall_congr'
  intro p
  have h := eq (point p.val).1 p.property.1
  simp only [HolAt,SatisfiesCR,connectionCoefficient,h.fderiv_eq]

/-- For the coefficient originally given, with smoothness only in a neighborhood
of the closed disk, every open base subdomain has all three chart Stein properties. -/
theorem chart_of_smooth_germ {σ : ℂ → ℝ} (simple : SimpleMetricGerm σ) (U : Set ℂ)
    (openU : IsOpen U) (inside : U ⊆ ball (0 : ℂ) 1) : HasSteinProperties σ U := by
  obtain ⟨τ,R,hR,same,valid⟩ := simple.extension
  have eq (z : ℂ) (hz : z ∈ U) : τ =ᶠ[𝓝 z] σ :=
    Filter.mem_of_superset (isOpen_ball.mem_nhds (ball_subset_ball hR.le (inside hz))) (fun _ hx => same hx)
  have hol (f : E → ℂ) := holOn_iff_of_germs (f := f) eq
  have tEq : tests σ U = tests τ U := by
    ext g
    simp only [tests,mem_setOf_eq,hol]
  have h := universal_chart τ valid U openU inside
  constructor
  · intro K hK; rw [tEq]; exact h.convex K hK
  · intro x y ne
    obtain ⟨f,hf,e⟩ := h.separates x y ne
    exact ⟨f,(hol f).mp hf,e⟩
  · intro x
    obtain ⟨f,g,hf,hg,e⟩ := h.coordinates x
    exact ⟨f,g,(hol f).mp hf,(hol g).mp hg,e⟩

/-- The physical atlas satisfies the ordinary manifold Stein conditions for this same metric germ. -/
theorem manifold_of_smooth_germ {σ : ℂ → ℝ} (simple : SimpleMetricGerm σ) (U : Set ℂ)
    (openU : IsOpen U) (inside : U ⊆ ball (0 : ℂ) 1) :
    ∃ A : ChartSteinAtlas.HolomorphicCover σ U, letI := A.chartedSpace openU
      IsManifold 𝓘(ℂ,E) 1 (ChartSteinAtlas.domain U) ∧ SteinCriterion.SteinConditions (ChartSteinAtlas.domain U) :=
  ManifoldStein.exists_stein_manifold openU inside (chart_of_smooth_germ simple U openU inside)

end TransportOkaGrauert.GeneralStein
