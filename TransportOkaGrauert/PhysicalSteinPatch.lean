import TransportOkaGrauert.PhysicalSteinExhaustion

/-! # Patching a bounded strictly plurisubharmonic function on a compact sublevel -/

noncomputable section
namespace TransportOkaGrauert.PhysicalSteinPatch

open Set Filter Metric ChartStein PhysicalStein CollarGluing
open scoped ContDiff Topology

theorem global_of_compact {σ : ℂ → ℝ} (simple : SimpleDiskTarget.SimpleMetric σ)
    (localPot : ∀ S : Set E, IsCompact S → S ⊆ domain → ∃ g : E → ℝ,
      (∀ p ∈ domain, ContDiffAt ℝ ∞ g p ∧ 0 ≤ g p ∧ g p ≤ 1) ∧
      ∀ p ∈ S, StrictAt (J σ) g p) :
    ∃ F : E → ℝ, (∀ p ∈ domain, ContDiffAt ℝ ∞ F p ∧ StrictAt (J σ) F p) ∧
      ∀ m : ℝ, IsCompact {p ∈ domain | F p ≤ m} := by
  obtain ⟨ρ,sρ,sub,K,hK,kd,exterior⟩ := simple_exhaustion simple
  obtain ⟨c,bc⟩ := hK.bddAbove_image (f := ρ) (fun p hp => (sρ p (kd hp)).continuousAt.continuousWithinAt)
  let S := {p ∈ domain | ρ p ≤ c+3}
  obtain ⟨g,sg,strict⟩ := localPot S (sub (c+3)) (fun _ h => h.1)
  let G := fun p => ρ p-c
  let F := blend g G
  have smoothF (p : E) (hp : p ∈ domain) : ContDiffAt ℝ ∞ F p :=
    blend_smooth (sg p hp).1 ((sρ p hp).sub (contDiffAt_const (c := c)))
  refine ⟨F,?_,?_⟩
  · intro p hp
    refine ⟨smoothF p hp,?_⟩
    apply strict_blend ((J_smooth simple.smooth hp.2).differentiableAt (by simp)) (J_sq σ hp.2)
      ((sg p hp).1.of_le (by decide)) (((sρ p hp).sub (contDiffAt_const (c := c))).of_le (by decide))
    · intro ht
      apply strict p ⟨hp,?_⟩
      change ρ p-c-g p < 1 at ht
      linarith [(sg p hp).2.2]
    · intro ht
      apply strict_sub_const _ c
      apply exterior p hp
      intro mem
      have := bc (mem_image_of_mem ρ mem)
      change 0 < ρ p-c-g p at ht
      linarith [(sg p hp).2.1]
  intro m
  let n := max (c+3) (m+c+1)
  let P := {p ∈ domain | ρ p ≤ n}
  letI : CompactSpace P := isCompact_iff_compactSpace.mp (sub n)
  have cf : Continuous (fun p : P => F p) := continuousOn_iff_continuous_restrict.mp
    (fun p hp => (smoothF p hp.1).continuousAt.continuousWithinAt)
  have closed : IsClosed {p : P | F p ≤ m} := isClosed_le cf continuous_const
  have eq : {p ∈ domain | F p ≤ m} = Subtype.val '' {p : P | F p ≤ m} := by
    ext p
    constructor
    · intro h
      obtain ⟨hp,hm⟩ := h
      have inside : ρ p ≤ n := by
        by_cases lo : ρ p ≤ c+3
        · exact lo.trans (le_max_left ..)
        have active : 1 ≤ G p-g p := by dsimp [G]; linarith [(sg p hp).2.2]
        change g p + ramp (G p-g p) ≤ m at hm
        rw [ramp_active active] at hm
        dsimp [G] at hm
        exact (show ρ p ≤ m+c+1 by linarith [ramp_nonneg 1]).trans (le_max_right ..)
      exact ⟨⟨p,hp,inside⟩,hm,rfl⟩
    · rintro ⟨q,hq,rfl⟩
      exact ⟨q.property.1,hq⟩
  rw [eq]
  exact closed.isCompact.image continuous_subtype_val

end TransportOkaGrauert.PhysicalSteinPatch
