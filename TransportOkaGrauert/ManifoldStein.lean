import TransportOkaGrauert.ChartSteinAtlas
import TransportOkaGrauert.SteinCriterion
import TransportOkaGrauert.FlatStein
import TransportOkaGrauert.HyperbolicStein
import TransportOkaGrauert.GeneralSteinReduction

/-!
# The three Stein properties on the physical complex manifold

The functions used to verify the fixed-chart transport equations become
manifold-holomorphic on the physical domain. The hull for all manifold-holomorphic
functions is closed and contained in the compact hull already obtained with
the transport test functions. The coordinate charts are pairs of globally
defined holomorphic functions.
-/

noncomputable section

namespace TransportOkaGrauert.ManifoldStein

open ChartStein ChartSteinAtlas Set Metric Filter Manifold
open scoped Topology ContDiff

local notation "I₂" => 𝓘(ℂ,E)
local notation "I₁" => 𝓘(ℂ,ℂ)

variable {σ : ℂ → ℝ} {U : Set ℂ}

/-- A global scalar solution of the two transport CR equations on the physical
domain is holomorphic in the constructed complex atlas. -/
theorem mdifferentiable_restrict (A : HolomorphicCover σ U) (hU : IsOpen U)
    {f : E → ℂ} (hf : ∀ y ∈ domain U, HolAt σ f y) :
    letI := A.chartedSpace hU
    MDifferentiable I₂ I₁ (fun y : domain U => f y.val) := by
  letI := A.chartedSpace hU
  letI := A.isManifold_one hU
  intro x
  let e := A.chart x
  let c := chartAt E x
  have hx : x ∈ c.source := mem_chart_source E x
  have dc : MDifferentiableAt I₂ I₂ c x :=
    ((contMDiffOn_chart (I := I₂) (n := 1)).contMDiffAt (c.open_source.mem_nhds hx)).mdifferentiableAt one_ne_zero
  have fy := A.holomorphic x f (fun y hy => hf y (A.source_subset x hy))
  have hy : e x.val ∈ e.target := e.map_source (A.centered x)
  have df : DifferentiableAt ℂ (f ∘ e.symm) (c x) := (fy _ hy).differentiableAt (e.open_target.mem_nhds hy)
  have hcomp := df.mdifferentiableAt.comp x dc
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [continuous_subtype_val.continuousAt.eventually (e.open_source.mem_nhds (A.centered x))]
    with y hy
  change f y.val = f (e.symm (e y.val))
  rw [e.left_inv hy]

/-- The chart-level axioms transfer to the true holomorphic hull, separation and
holomorphic local diffeomorphisms for the complex manifold on the physical domain. -/
theorem steinConditions (A : HolomorphicCover σ U) (hU : IsOpen U) (hs : U ⊆ ball 0 1)
    (h : HasSteinProperties σ U) :
    letI := A.chartedSpace hU
    SteinCriterion.SteinConditions (domain U) := by
  letI := A.chartedSpace hU
  letI := A.isManifold_one hU
  let e := interiorHomeomorph hs
  have regular {f : E → ℂ} (hf : HolOn σ U f) :
      (fun y : domain U => f y.val) ∈ SteinCriterion.holomorphicFunctions (domain U) :=
    mdifferentiable_restrict A hU (fun y hy => hf (e ⟨y,hy⟩))
  constructor
  · intro K hK
    let H := DivisorHull.testHull (SteinCriterion.holomorphicFunctions (domain U)) K
    let C := DivisorHull.testHull (tests σ U) (e '' K)
    have hc : IsCompact C := h.convex _ (hK.image e.continuous)
    have closedH : IsClosed H := DivisorHull.isClosed_testHull
      (fun _ hg => MDifferentiable.continuous hg) K
    apply (e.isClosedEmbedding.isCompact_preimage hc).of_isClosed_subset closedH
    intro x hx
    change e x ∈ DivisorHull.testHull (tests σ U) (e '' K)
    intro g hg b bound
    obtain ⟨f,hf,eq⟩ := hg
    rw [eq]
    exact hx (fun y : domain U => f y.val) (regular hf) b (fun k hk => by
      simpa only [eq] using bound (e k) (mem_image_of_mem e hk))
  · intro x y hxy
    obtain ⟨f,hf,sep⟩ := h.separates (e x) (e y) (fun h => hxy (e.injective h))
    exact ⟨_,regular hf,sep⟩
  · intro x
    let c := chartAt E x
    let f (y : domain U) := (A.chart x y.val).1
    let g (y : domain U) := (A.chart x y.val).2
    have hf : MDifferentiable I₂ I₁ f := mdifferentiable_restrict A hU (fun y hy => (A.components x y hy).1)
    have hg : MDifferentiable I₂ I₁ g := mdifferentiable_restrict A hU (fun y hy => (A.components x y hy).2)
    let φ : PartialDiffeomorph I₂ I₂ (domain U) E 1 := {
      toPartialEquiv := c.toPartialEquiv
      open_source := c.open_source
      open_target := c.open_target
      contMDiffOn_toFun := contMDiffOn_chart
      contMDiffOn_invFun := contMDiffOn_chart_symm }
    exact ⟨f,hf,g,hg,φ,mem_chart_source E x,fun _ _ => rfl⟩

/-- Existence of a manifold structure satisfying the three ordinary Stein conditions,
on the original topology of the prescribed physical domain. -/
theorem exists_stein_manifold (hU : IsOpen U) (hs : U ⊆ ball 0 1) (h : HasSteinProperties σ U) :
    ∃ A : HolomorphicCover σ U, letI := A.chartedSpace hU
      IsManifold I₂ 1 (domain U) ∧ SteinCriterion.SteinConditions (domain U) := by
  obtain ⟨A⟩ := cover_of_stein hU hs h
  exact ⟨A,A.isManifold_one hU,steinConditions A hU hs h⟩

/-- The simple metric reduction concludes the ordinary manifold Stein properties
once the scalar transport equation and radial-frame construction are supplied. -/
theorem of_scalar_and_geometry (simple : SimpleDiskTarget.SimpleMetric σ)
    (solve : PencilLifts.ScalarSolvability σ)
    (radial : ∀ a : ClosedDisk, Nonempty (PencilGeometry.Data σ a))
    (hU : IsOpen U) (hs : U ⊆ ball 0 1) :
    ∃ A : HolomorphicCover σ U, letI := A.chartedSpace hU
      IsManifold I₂ 1 (domain U) ∧ SteinCriterion.SteinConditions (domain U) :=
  exists_stein_manifold hU hs (GeneralSteinReduction.for_metric simple solve radial U hU hs)

/-- Every flat constant conformal factor gives an actual manifold satisfying the
three Stein properties on every open base subdomain. -/
theorem flat (k : ℝ) (hU : IsOpen U) (hs : U ⊆ ball 0 1) :
    ∃ A : HolomorphicCover (fun _ => k) U, letI := A.chartedSpace hU
      IsManifold I₂ 1 (domain U) ∧ SteinCriterion.SteinConditions (domain U) :=
  exists_stein_manifold hU hs (FlatStein.constant_conformal_factor k U hU hs)

/-- The whole Poincaré family with 0 < c < 1 has the ordinary manifold Stein
properties on every open base subdomain. -/
theorem poincare {c : ℝ} (hc : 0<c) (h1 : c<1) (hU : IsOpen U) (hs : U ⊆ ball 0 1) :
    ∃ A : HolomorphicCover (HyperbolicCR.factor c) U, letI := A.chartedSpace hU
      IsManifold I₂ 1 (domain U) ∧ SteinCriterion.SteinConditions (domain U) :=
  exists_stein_manifold hU hs (HyperbolicStein.poincare_disk hc h1 U hU hs)

/-- Universal endpoint on the physical complex manifold of the conformal disk. -/
def GeneralManifoldStatement : Prop :=
  ∀ σ : ℂ → ℝ, SimpleDiskTarget.SimpleMetric σ → ∀ U : Set ℂ, ∀ hU : IsOpen U,
    U ⊆ ball 0 1 → ∃ A : HolomorphicCover σ U, letI := A.chartedSpace hU
      IsManifold I₂ 1 (domain U) ∧ SteinCriterion.SteinConditions (domain U)

theorem manifold_of_chart (h : GeneralSimpleSurfaceStatement) : GeneralManifoldStatement :=
  fun σ simple U hU hs => exists_stein_manifold hU hs (h σ simple U hU hs)

end TransportOkaGrauert.ManifoldStein
