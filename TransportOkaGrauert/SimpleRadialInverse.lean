import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! # Global inversion on the star of first-exit velocities

Let a smooth endpoint map be given on the velocities before first exit.
The closure of the star of velocities is compact and its boundary is sent
to the boundary of the base disk. A nonsingular endpoint differential on
the open star makes the endpoint map a covering; the base disk is simply
connected, so it admits a single smooth inverse on the entire disk.
-/

noncomputable section
namespace TransportOkaGrauert.SimpleRadialInverse

open Set Metric Filter Topology
open scoped ContDiff Topology

private theorem bijective_of_proper_localHomeomorph {E X : Type*}
    [TopologicalSpace E] [TopologicalSpace X] [T2Space E] [ConnectedSpace E]
    [SimplyConnectedSpace X] [LocPathConnectedSpace X]
    {f : E → X} (proper : IsProperMap f) (loc : IsLocalHomeomorph f) : Function.Bijective f := by
  have cov : IsCoveringMap f := by
    intro x
    have localSections (e : E) (_ : e ∈ f ⁻¹' {x}) :
        ∃ φ : OpenPartialHomeomorph E X, e ∈ φ.source ∧ (φ : E → X) = f := by
      obtain ⟨φ, h, heq⟩ := loc e
      exact ⟨φ, h, heq.symm⟩
    exact proper.isClosedMap.isEvenlyCovered_of_openPartialHomeomorph
      ((proper.isCompact_preimage isCompact_singleton).finite
        (.of_openPartialHomeomorph f Subset.rfl localSections)) localSections
  let e : E := Classical.arbitrary E
  obtain ⟨g, ⟨hbase, hright⟩, _⟩ :=
    cov.existsUnique_continuousMap_lifts (ContinuousMap.id X) (f e) e rfl
  have right (x : X) : f (g x) = x := congrFun hright x
  have left : (g ∘ f) = id := cov.eq_of_comp_eq (g.continuous.comp proper.continuous)
    continuous_id (funext fun x => right (f x)) e hbase
  exact ⟨(show Function.LeftInverse g f from fun x => congrFun left x).injective,
    (show Function.RightInverse g f from right).surjective⟩

/-- The ordinary exponential-map conclusion from compactness of the closed
first-exit star, star-shapedness of the in-disk velocities, and the absence
of critical velocities. The inverse is smooth on the target ball, including
all points of any smaller closed disk. -/
theorem smooth_inverse_on_disk {f : ℂ → ℂ} {K : Set ℂ} {R : ℝ} (hR : 0 < R)
    (hK : IsCompact K) (hf : ContinuousOn f K)
    (hopen : IsOpen (K ∩ f ⁻¹' ball (0 : ℂ) R))
    (hstar : StarConvex ℝ 0 (K ∩ f ⁻¹' ball (0 : ℂ) R))
    (hzero : (0 : ℂ) ∈ K ∩ f ⁻¹' ball (0 : ℂ) R)
    (smooth : ∀ x ∈ K ∩ f ⁻¹' ball (0 : ℂ) R, ContDiffAt ℝ ∞ f x)
    (regular : ∀ x ∈ K ∩ f ⁻¹' ball (0 : ℂ) R, Function.Bijective (fderiv ℝ f x)) :
    ∃ L : ℂ → ℂ, ContDiffOn ℝ ∞ L (ball (0 : ℂ) R) ∧
      (∀ y ∈ ball (0 : ℂ) R, L y ∈ K ∧ f (L y) = y) ∧
      ∀ x ∈ K, f x ∈ ball (0 : ℂ) R → L (f x) = x := by
  classical
  let B := ball (0 : ℂ) R
  let D := K ∩ f ⁻¹' B
  let F (x : D) : B := ⟨f x, x.property.2⟩
  have derivEq (x : ℂ) (hx : x ∈ D) : ∃ e : ℂ ≃L[ℝ] ℂ, HasFDerivAt f e.toContinuousLinearMap x :=
    ⟨ContinuousLinearEquiv.ofBijective (fderiv ℝ f x)
      (LinearMap.ker_eq_bot.mpr (regular x hx).1) (LinearMap.range_eq_top.mpr (regular x hx).2),
      ((smooth x hx).differentiableAt (by simp)).hasFDerivAt⟩
  have ambient : IsLocalHomeomorphOn f D := by
    intro x hx
    obtain ⟨e, he⟩ := derivEq x hx
    exact ⟨(smooth x hx).toOpenPartialHomeomorph f he (by simp),
      (smooth x hx).mem_toOpenPartialHomeomorph_source he (by simp), rfl⟩
  have hlocVal := hopen.isOpenEmbedding_subtypeVal.isLocalHomeomorph
  have compLoc : IsLocalHomeomorph (Subtype.val ∘ F : D → ℂ) :=
    isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mpr
      (ambient.comp hlocVal.isLocalHomeomorphOn (fun x _ => x.property))
  have hcont : Continuous F := Continuous.subtype_mk
    (f := fun x : D => f x) (ambient.continuousOn.restrict) _
  have loc : IsLocalHomeomorph F := compLoc.of_comp isOpen_ball.isOpenEmbedding_subtypeVal.isLocalHomeomorph hcont
  have proper : IsProperMap F := by
    apply isProperMap_iff_isCompact_preimage.mpr
    refine ⟨hcont, ?_⟩
    intro C hC
    rw [Subtype.isCompact_iff]
    have hc' : IsCompact (Subtype.val '' C : Set ℂ) := hC.image continuous_subtype_val
    have eq : Subtype.val '' (F ⁻¹' C) = K ∩ f ⁻¹' (Subtype.val '' C) := by
      ext x
      constructor
      · rintro ⟨v, hv, rfl⟩
        exact ⟨v.property.1, F v, hv, rfl⟩
      · rintro ⟨hx, y, hy, he⟩
        have hb : f x ∈ B := he ▸ y.property
        exact ⟨⟨x,hx,hb⟩, show F _ ∈ C from (show F ⟨x,hx,hb⟩ = y from Subtype.ext he.symm) ▸ hy, rfl⟩
    rw [eq]
    exact hK.of_isClosed_subset (hf.preimage_isClosed_of_isClosed hK.isClosed hc'.isClosed) inter_subset_left
  letI : ContractibleSpace B := contractibleSpace_ball hR
  letI : LocPathConnectedSpace B := isOpen_ball.locPathConnectedSpace
  letI : ConnectedSpace D := isConnected_iff_connectedSpace.mp (hstar.isPathConnected hzero).isConnected
  let G := loc.toHomeomorphOfBijective (bijective_of_proper_localHomeomorph proper loc)
  let L (y : ℂ) := if hy : y ∈ B then (G.symm ⟨y,hy⟩).val else 0
  have left (x : ℂ) (hx : x ∈ D) : L (f x) = x := by
    have he := G.symm_apply_apply (⟨x,hx⟩ : D)
    have hb : f x ∈ B := hx.2
    rw [show L (f x) = (G.symm ⟨f x,hb⟩).val by simp [L, hb]]
    exact congrArg Subtype.val he
  have right (y : ℂ) (hy : y ∈ B) : L y ∈ D ∧ f (L y) = y := by
    have he := G.apply_symm_apply (⟨y,hy⟩ : B)
    rw [show L y = (G.symm ⟨y,hy⟩).val by simp [L, hy]]
    exact ⟨(G.symm ⟨y,hy⟩).property, congrArg Subtype.val he⟩
  refine ⟨L, ?_, fun y hy => ⟨(right y hy).1.1,(right y hy).2⟩, fun x hx h => left x ⟨hx,h⟩⟩
  intro y hy
  obtain ⟨hx, heq⟩ := right y hy
  obtain ⟨e, he⟩ := derivEq _ hx
  have hs := smooth _ hx
  have hl := hs.to_localInverse he (by simp)
  have eq := (hs.hasStrictFDerivAt' he (by simp)).localInverse_unique
    (g := L) (Filter.eventually_of_mem (hopen.mem_nhds hx) left)
  rw [← heq]
  exact (hl.congr_of_eventuallyEq eq).contDiffWithinAt

end TransportOkaGrauert.SimpleRadialInverse
