import TransportOkaGrauert.SteinCriterion

/-! # Invariance of the Stein conditions under a complex diffeomorphism -/
namespace TransportOkaGrauert.SteinBiholomorphic
open SteinCriterion DivisorHull Set Manifold
open scoped ContDiff
local notation "I₂" => 𝓘(ℂ, Plane)
variable {X Y : Type*} [TopologicalSpace X] [ChartedSpace Plane X] [TopologicalSpace Y] [ChartedSpace Plane Y]

private theorem precompose_local (e : Diffeomorph I₂ I₂ X Y 1) {f : Y → Plane} {x : X}
    (h : IsLocalDiffeomorphAt I₂ I₂ 1 f (e x)) :
    IsLocalDiffeomorphAt I₂ I₂ 1 (f ∘ e) x := by
  obtain ⟨c,hx,same⟩ := h
  let v : PartialDiffeomorph I₂ I₂ X Plane 1 := {
    toFun := c ∘ e
    invFun := e.symm ∘ c.invFun
    source := e ⁻¹' c.source
    target := c.target
    map_source' := fun _ hi => c.map_source hi
    map_target' := fun y hy => by change e (e.symm (c.invFun y)) ∈ c.source; rw [e.apply_symm_apply]; exact c.map_target hy
    left_inv' := fun t ht => (congrArg e.symm (c.left_inv ht)).trans (e.symm_apply_apply t)
    right_inv' := fun t ht => by change c (e (e.symm (c.invFun t))) = t; rw [e.apply_symm_apply]; exact c.right_inv ht
    open_source := c.open_source.preimage e.continuous
    open_target := c.open_target
    contMDiffOn_toFun := c.contMDiffOn_toFun.comp e.contMDiff.contMDiffOn (fun _ ht => ht)
    contMDiffOn_invFun := e.symm.contMDiff.comp_contMDiffOn c.contMDiffOn_invFun }
  exact ⟨v,hx,fun t ht => same ht⟩

/-- Pulling back all holomorphic functions carries the holomorphic hull exactly onto the hull. -/
theorem hull_eq (e : Diffeomorph I₂ I₂ X Y 1) (K : Set X) :
    testHull (holomorphicFunctions X) K = e.symm '' testHull (holomorphicFunctions Y) (e '' K) := by
  ext x
  constructor
  · intro hx
    refine ⟨e x,?_,e.symm_apply_apply x⟩
    intro f hf b bound
    apply hx (f ∘ e) (hf.comp (e.mdifferentiable one_ne_zero)) b
    exact fun t ht => bound _ ⟨t,ht,rfl⟩
  · rintro ⟨y,hy,rfl⟩ f hf b bound
    apply hy (f ∘ e.symm) (hf.comp (e.symm.mdifferentiable one_ne_zero)) b
    rintro _ ⟨t,ht,rfl⟩
    simpa using bound t ht

/-- A complex diffeomorphism transfers holomorphic convexity, separation and global functions
giving local coordinates to the source manifold. -/
theorem pullback (e : Diffeomorph I₂ I₂ X Y 1) (s : SteinConditions Y) : SteinConditions X where
  compactHull K hK := by
    rw [hull_eq e]
    exact (s.compactHull _ (hK.image e.continuous)).image e.symm.continuous
  separate x y h := by
    obtain ⟨f,hf,d⟩ := s.separate (e x) (e y) (fun eq => h (e.injective eq))
    exact ⟨f ∘ e,hf.comp (e.mdifferentiable one_ne_zero),d⟩
  coordinates x := by
    obtain ⟨f,hf,g,hg,h⟩ := s.coordinates (e x)
    exact ⟨f ∘ e,hf.comp (e.mdifferentiable one_ne_zero),g ∘ e,hg.comp (e.mdifferentiable one_ne_zero),
      precompose_local e h⟩

theorem iff (e : Diffeomorph I₂ I₂ X Y 1) : SteinConditions X ↔ SteinConditions Y :=
  ⟨pullback e.symm,pullback e⟩

end TransportOkaGrauert.SteinBiholomorphic
