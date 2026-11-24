import TransportOkaGrauert.SimpleEnlargement

/-! # Simple conformal metrics defined on a neighborhood of the closed disk

A coefficient is represented by a total function. Only its smooth germ on
the closed disk is used. The original escaping geodesics are shortened
before leaving a collar on which the global smooth extension agrees. -/
noncomputable section
namespace TransportOkaGrauert.SimpleDiskTarget
open Complex Metric Set Filter
open scoped ContDiff Topology

/-- Fixed-chart simplicity for a coefficient smooth on an open neighborhood
of the closed disk. Its representative may be arbitrary farther outside. -/
structure SimpleMetricGerm (σ : ℂ → ℝ) : Prop where
  smooth : ∃ V : Set ℂ, IsOpen V ∧ closedBall 0 1 ⊆ V ∧ ContDiffOn ℝ ∞ σ V
  strictConvex : ∀ z ∈ sphere (0 : ℂ) 1, 0 < 1 + fderiv ℝ σ z z
  escapes : ∀ z₀ ∈ closedBall (0 : ℂ) 1, ∀ θ₀ : ℝ, ∃ a b : ℝ, ∃ z θ,
    a < 0 ∧ 0 < b ∧ z 0 = z₀ ∧ θ 0 = θ₀ ∧ unitGeodesicOn σ z θ (Icc a b) ∧
      1 < ‖z a‖ ∧ 1 < ‖z b‖
  noConjugate : ∀ a b : ℝ, a < b → ∀ z θ, unitGeodesicOn σ z θ (Icc a b) →
    (∀ t ∈ Icc a b, z t ∈ closedBall 0 1) →
    ∀ j dj : ℝ → ℝ, jacobiOn σ z j dj (Icc a b) → j a = 0 → j b = 0 →
      ∀ t ∈ Icc a b, j t = 0

namespace SimpleMetricGerm

/-- Smooth neighborhoods may be chosen separately at each point of the closed disk. -/
theorem smooth_neighborhood_of_local {σ : ℂ → ℝ}
    (h : ∀ z ∈ closedBall (0:ℂ) 1, ∃ V : Set ℂ, IsOpen V ∧ z ∈ V ∧ ContDiffOn ℝ ∞ σ V) :
    ∃ V : Set ℂ, IsOpen V ∧ closedBall 0 1 ⊆ V ∧ ContDiffOn ℝ ∞ σ V := by
  let W := {V : Set ℂ | IsOpen V ∧ ContDiffOn ℝ ∞ σ V}
  refine ⟨⋃₀ W,isOpen_sUnion (fun V hV => hV.1),?_,?_⟩
  · intro z hz
    obtain ⟨V,openV,hzV,sV⟩ := h z hz
    exact mem_sUnion.mpr ⟨V,⟨openV,sV⟩,hzV⟩
  · intro z hz
    obtain ⟨V,hV,hzV⟩ := mem_sUnion.mp hz
    exact ((hV.2.contDiffAt (hV.1.mem_nhds hzV))).contDiffWithinAt

theorem of_simple {σ : ℂ → ℝ} (h : SimpleMetric σ) : SimpleMetricGerm σ :=
  ⟨⟨univ,isOpen_univ,subset_univ _,h.smooth.contDiffOn⟩,h.strictConvex,h.escapes,h.noConjugate⟩

private theorem truncate_forward {z : ℝ → ℂ} {b R : ℝ} (hb : 0 < b) (hR : 1 < R)
    (cont : ContinuousOn z (Icc 0 b)) (start : ‖z 0‖ ≤ 1) (outside : 1 < ‖z b‖) :
    ∃ t ∈ Ioc 0 b, 1 < ‖z t‖ ∧ ∀ s ∈ Icc 0 t, ‖z s‖ < R := by
  let r := min ‖z b‖ ((1+R)/2)
  have big : 1 < r := lt_min outside (by linarith)
  have small : r < R := (min_le_right _ _).trans_lt (by linarith)
  let S := Icc 0 b ∩ (fun t => ‖z t‖) ⁻¹' ({r} : Set ℝ)
  have reach (u : ℝ) (hu : u ∈ Icc 0 b) (hu' : r ≤ ‖z u‖) :
      ∃ v ∈ Icc 0 u, ‖z v‖ = r :=
    intermediate_value_Icc hu.1 (cont.norm.mono (Icc_subset_Icc_right hu.2)) ⟨start.trans big.le,hu'⟩
  obtain ⟨v,hv,ev⟩ := reach b (right_mem_Icc.mpr hb.le) (min_le_left _ _)
  have closed : IsClosed S := cont.norm.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have least := (isCompact_Icc.of_isClosed_subset closed inter_subset_left).isLeast_sInf
    (show S.Nonempty from ⟨v,hv,ev⟩)
  have eq : ‖z (sInf S)‖ = r := least.1.2
  have pos : 0 < sInf S := lt_of_le_of_ne least.1.1.1 (fun e => by rw [← e] at eq; linarith)
  refine ⟨sInf S,⟨pos,least.1.1.2⟩,eq.symm ▸ big,?_⟩
  intro s hs
  rcases hs.2.eq_or_lt with he | hl
  · simpa [he,eq] using small
  by_contra! far
  have sb := hs.2.trans least.1.1.2
  obtain ⟨v,hv,ev⟩ := reach s ⟨hs.1,sb⟩ (small.le.trans far)
  exact (not_lt_of_ge (least.2 (show v ∈ S from ⟨⟨hv.1,hv.2.trans sb⟩,ev⟩))) (hv.2.trans_lt hl)

private theorem curvature_germ {σ τ : ℂ → ℝ} {z : ℂ} (eq : τ =ᶠ[𝓝 z] σ) :
    curvature τ z = curvature σ z := by
  have d (v : ℂ) : (fun y => fderiv ℝ τ y v) =ᶠ[𝓝 z] (fun y => fderiv ℝ σ y v) := by
    filter_upwards [eq.eventually_nhds] with y hy
    have near : τ =ᶠ[𝓝 y] σ := hy
    rw [near.fderiv_eq]
  simp only [curvature,laplacian,eq.eq_of_nhds,(d 1).fderiv_eq,(d I).fderiv_eq]

private theorem transfer_ray {σ τ : ℂ → ℝ} {z θ s u} (ray : unitGeodesicOn σ z θ s)
    (sub : u ⊆ s) (germ : ∀ t ∈ u, τ =ᶠ[𝓝 (z t)] σ) : unitGeodesicOn τ z θ u := by
  intro t ht
  have eq := germ t ht
  simpa only [Isothermal.angularDrift,eq.eq_of_nhds,eq.fderiv_eq] using
    And.intro ((ray t (sub ht)).1.mono sub) ((ray t (sub ht)).2.mono sub)

/-- A globally smooth simple extension with identical coefficients on a full collar. -/
theorem extension {σ : ℂ → ℝ} (h : SimpleMetricGerm σ) :
    ∃ (τ : ℂ → ℝ) (R : ℝ), 1 < R ∧ EqOn τ σ (ball 0 R) ∧ SimpleMetric τ := by
  obtain ⟨V,openV,inV,smoothV⟩ := h.smooth
  obtain ⟨ε,hε,collar⟩ := (isCompact_closedBall (0:ℂ) 1).exists_cthickening_subset_open openV inV
  have inCollar : closedBall (0:ℂ) (ε+1) ⊆ V := by
    simpa only [cthickening_closedBall hε.le zero_le_one] using collar
  let R := 1+ε/3
  let β : ContDiffBump (0 : ℂ) := ⟨R,1+2*ε/3,by dsimp [R]; linarith,by dsimp [R]; linarith⟩
  let τ := fun z => β z * σ z
  have hR : 1 < R := by dsimp [R]; linarith
  have eqOn : EqOn τ σ (ball 0 R) :=
    fun _ hz => by simp [τ,β.one_of_mem_closedBall (ball_subset_closedBall hz)]
  have germ {z} (hz : ‖z‖ < R) : τ =ᶠ[𝓝 z] σ :=
    Filter.mem_of_superset (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hz)) (fun x hx => eqOn hx)
  have sτ : ContDiff ℝ ∞ τ := by
    apply contDiff_iff_contDiffAt.mpr
    intro z
    by_cases hz : z ∈ ball (0:ℂ) (ε+1)
    · have hv := inCollar (ball_subset_closedBall hz)
      exact β.contDiff.contDiffAt.mul (smoothV.contDiffAt (openV.mem_nhds hv))
    · have far : β.rOut < ‖z‖ := by
        have bound := le_of_not_gt (fun p => hz (mem_ball_zero_iff.mpr p))
        change 1+2*ε/3 < _; linarith
      apply (contDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq
      filter_upwards [continuous_norm.continuousAt.eventually_const_lt far] with y hy
      simp [τ,β.zero_of_le_dist (x := y) (by simpa using hy.le)]
  refine ⟨τ,R,hR,eqOn,⟨sτ,?_,?_,?_⟩⟩
  · intro z hz
    have eq := germ ((mem_sphere_zero_iff_norm.mp hz).trans_lt hR)
    simpa only [eq.fderiv_eq] using h.strictConvex z hz
  · intro z₀ hz₀ θ₀
    obtain ⟨a,b,z,θ,ha,hb,z0,θ0,ray,oa,ob⟩ := h.escapes z₀ hz₀ θ₀
    have c : ContinuousOn z (Icc a b) := fun t ht => (ray t ht).1.continuousWithinAt
    have zstart : ‖z 0‖ ≤ 1 := z0 ▸ mem_closedBall_zero_iff.mp hz₀
    have cm : ContinuousOn (fun t => z (-t)) (Icc 0 (-a)) :=
      c.comp continuous_neg.continuousOn (fun t ht => ⟨by linarith [ht.2],by linarith [ht.1]⟩)
    obtain ⟨l,hl,el,insideL⟩ := truncate_forward (b := -a) (by linarith) hR cm
      (by simpa using zstart) (by simpa using oa)
    obtain ⟨u,hu,eu,insideU⟩ := truncate_forward hb hR (c.mono (Icc_subset_Icc_left ha.le)) zstart ob
    have sub : Icc (-l) u ⊆ Icc a b := Icc_subset_Icc (by linarith [hl.2]) hu.2
    refine ⟨-l,u,z,θ,by linarith [hl.1],hu.1,z0,θ0,transfer_ray ray sub ?_,el,eu⟩
    intro t ht
    apply germ
    by_cases sign : 0 ≤ t
    · exact insideU t ⟨sign,ht.2⟩
    · simpa only [neg_neg] using insideL (-t) ⟨by linarith,by linarith [ht.1]⟩
  · intro a b hab z θ ray stay j dj jac ja jb
    have eq (t : ℝ) (ht : t ∈ Icc a b) := germ ((mem_closedBall_zero_iff.mp (stay t ht)).trans_lt hR)
    apply h.noConjugate a b hab z θ (transfer_ray ray Subset.rfl fun t ht => (eq t ht).symm) stay j dj _ ja jb
    intro t ht
    simpa only [curvature_germ (eq t ht)] using jac t ht

end SimpleMetricGerm
end TransportOkaGrauert.SimpleDiskTarget
