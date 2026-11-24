import TransportOkaGrauert.GeneralStein
import TransportOkaGrauert.SteinBiholomorphic
import TransportOkaGrauert.IsothermalTangentDisk

/-! # Steinness on the intrinsic open unit tangent disk of an isothermal simple surface -/
noncomputable section
namespace TransportOkaGrauert.IntrinsicDiskStein
open Set Metric Manifold ChartedSpace SteinCriterion IsothermalTangentDisk
open scoped Manifold ContDiff Topology
local notation "I₂" => 𝓘(ℂ, Plane)
local notation "I₀" => 𝓘(ℝ, ℂ)

section pullback
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [ChartedSpace Plane Y]

/-- The atlas on X obtained by precomposing every chart on Y with the fixed homeomorphism. -/
def pullbackAtlas (e : X ≃ₜ Y) : ChartedSpace Plane X where
  atlas := e.transOpenPartialHomeomorph '' atlas Plane Y
  chartAt x := e.transOpenPartialHomeomorph (chartAt Plane (e x))
  mem_chart_source x := mem_chart_source Plane (e x)
  chart_mem_atlas x := ⟨_,chart_mem_atlas Plane (e x),rfl⟩

omit [ChartedSpace Plane Y] in
private theorem transition (e : X ≃ₜ Y) (f g : OpenPartialHomeomorph Y Plane) :
    (e.transOpenPartialHomeomorph f).symm.trans (e.transOpenPartialHomeomorph g) = f.symm.trans g := by
  apply OpenPartialHomeomorph.ext
  · intro x
    exact congrArg g (e.apply_symm_apply (f.symm x))
  · intro x
    exact congrArg f (e.apply_symm_apply (g.symm x))
  · ext x
    change (x ∈ f.target ∧ e (e.symm (f.symm x)) ∈ g.source) ↔ _
    rw [e.apply_symm_apply]
    rfl

theorem pullback_manifold (e : X ≃ₜ Y) [IsManifold I₂ 1 Y] :
    letI := pullbackAtlas e
    IsManifold I₂ 1 X := by
  letI := pullbackAtlas e
  refine { compatible := ?_ }
  rintro _ _ ⟨f,hf,rfl⟩ ⟨g,hg,rfl⟩
  rw [transition]
  exact (contDiffGroupoid 1 I₂).compatible hf hg

omit [ChartedSpace Plane Y] in
private theorem chart_self_smooth (c : OpenPartialHomeomorph Y Plane) (p : Y) (hp : p ∈ c.source) :
    ContDiffAt ℂ 1 (fun z => c (c.symm z)) (c p) := by
  apply contDiffAt_id.congr_of_eventuallyEq
  filter_upwards [c.open_target.mem_nhds (c.map_source hp)] with z hz using c.right_inv hz

/-- The given homeomorphism becomes a complex diffeomorphism for the pullback atlas. -/
def pullbackDiffeomorph (e : X ≃ₜ Y) :
    letI := pullbackAtlas e
    Diffeomorph I₂ I₂ X Y 1 := by
  letI := pullbackAtlas e
  refine {toEquiv := e.toEquiv,contMDiff_toFun := ?_,contMDiff_invFun := ?_}
  · intro x
    apply contMDiffAt_iff.mpr
    refine ⟨e.continuous.continuousAt,?_⟩
    let c := chartAt Plane (e x)
    change ContDiffWithinAt ℂ 1 (fun z => c (e (e.symm (c.symm z)))) _ (c (e x))
    simp only [e.apply_symm_apply]
    exact (chart_self_smooth c (e x) (mem_chart_source Plane _)).contDiffWithinAt
  · intro y
    apply contMDiffAt_iff.mpr
    refine ⟨e.symm.continuous.continuousAt,?_⟩
    change ContDiffWithinAt ℂ 1 (fun z => (chartAt Plane (e (e.symm y))) (e (e.symm ((chartAt Plane y).symm z)))) _ ((chartAt Plane y) y)
    simp only [e.apply_symm_apply]
    exact (chart_self_smooth _ y (mem_chart_source Plane _)).contDiffWithinAt

end pullback

/-- A smooth isothermal chart for an abstract Riemannian surface identifies its actual
unit tangent disk with the transport twistor domain by a complex diffeomorphism.
The chart chooses the positive orientation on its source. The holomorphic atlas
is placed on the tangent disk's inherited topology. -/
theorem intrinsic {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold I₀ ∞ M]
    {g : Bundle.RiemannianMetric (TangentSpace I₀ : M → Type _)} {e : OpenPartialHomeomorph M ℂ} {σ : ℂ → ℝ}
    (metric : IsothermalFor g e σ) (he : ContMDiffOn I₀ I₀ ∞ e e.source)
    (hi : ContMDiffOn I₀ I₀ ∞ e.symm e.target) (simple : SimpleDiskTarget.SimpleMetric σ)
    {U : Set ℂ} (hU : IsOpen U) (sub : U ⊆ e.target) (inside : U ⊆ ball 0 1) :
    ∃ A : ChartSteinAtlas.HolomorphicCover σ U,
      letI := A.chartedSpace hU
      let t := diskHomeomorph metric he hi simple.smooth.continuous U sub
      letI := pullbackAtlas t
      IsManifold I₂ 1 (intrinsicDisk g e U) ∧
      SteinConditions (intrinsicDisk g e U) ∧
      ∃ d : Diffeomorph I₂ I₂ (intrinsicDisk g e U) (ChartSteinAtlas.domain U) 1, d.toHomeomorph = t := by
  obtain ⟨A,target,s⟩ := GeneralStein.universal_manifold σ simple U hU inside
  refine ⟨A,?_⟩
  letI := A.chartedSpace hU
  letI : IsManifold I₂ 1 (ChartSteinAtlas.domain U) := target
  let t := diskHomeomorph metric he hi simple.smooth.continuous U sub
  letI := pullbackAtlas t
  let d := pullbackDiffeomorph t
  exact ⟨pullback_manifold t,SteinBiholomorphic.pullback d s,d,rfl⟩

end TransportOkaGrauert.IntrinsicDiskStein
