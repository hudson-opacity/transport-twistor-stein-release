import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Order.Compact

/-!
# Compact hulls from boundary divisors

For a compact set, testing every upper bound for each function gives the usual
holomorphic hull when the test family is the algebra of holomorphic functions.
The proof below uses only continuity of the tests and membership of certain
reciprocals in that family.
-/

namespace TransportOkaGrauert.DivisorHull

open Set Topology

/-- Points satisfying every modulus bound on `K` given by a test function. -/
def testHull {U : Type*} (tests : Set (U → ℂ)) (K : Set U) : Set U :=
  {x | ∀ f ∈ tests, ∀ b : ℝ, (∀ k ∈ K, ‖f k‖ ≤ b) → ‖f x‖ ≤ b}

theorem isClosed_testHull {U : Type*} [TopologicalSpace U]
    {tests : Set (U → ℂ)} (continuousTests : ∀ f ∈ tests, Continuous f) (K : Set U) :
    IsClosed (testHull tests K) := by
  have h : testHull tests K =
      ⋂ f ∈ tests, ⋂ b ∈ {b : ℝ | ∀ k ∈ K, ‖f k‖ ≤ b}, {x | ‖f x‖ ≤ b} := by
    ext x
    simp only [testHull, mem_setOf_eq, mem_iInter]
  rw [h]
  exact isClosed_biInter fun f hf => isClosed_biInter fun _ _ =>
    isClosed_le (continuousTests f hf).norm continuous_const

/-- If every omitted point admits a continuous divisor that vanishes there, is
nonvanishing on `U`, and has a reciprocal in the test family, then every compact
set in `U` has compact test hull. The ambient space may be any compact space. -/
theorem isCompact_testHull_of_boundary_divisors
    {X : Type*} [TopologicalSpace X] [CompactSpace X] {U : Set X}
    {tests : Set (U → ℂ)} (continuousTests : ∀ f ∈ tests, Continuous f)
    (detectors : ∀ p ∉ U, ∃ q : X → ℂ, Continuous q ∧ q p = 0 ∧
      (∀ u : U, q u ≠ 0) ∧ (fun u : U => (q u)⁻¹) ∈ tests)
    {K : Set U} (compactK : IsCompact K) :
    IsCompact (testHull tests K) := by
  let H := testHull tests K
  have inside : closure (Subtype.val '' H) ⊆ U := by
    intro p hp
    by_contra hpU
    obtain ⟨q, hq, hzero, hnonzero, htest⟩ := detectors p hpU
    let f : U → ℂ := fun u => (q u)⁻¹
    obtain ⟨b, hb⟩ := compactK.bddAbove_image (continuousTests f htest).norm.continuousOn
    have bound : ∀ k ∈ K, ‖f k‖ ≤ b := fun k hk =>
      hb (mem_image_of_mem (fun u => ‖f u‖) hk)
    have avoid : Subtype.val '' H ⊆ {x : X | 1 ≤ b * ‖q x‖} := by
      rintro _ ⟨u, hu, rfl⟩
      have h := hu f htest b bound
      change ‖(q u)⁻¹‖ ≤ b at h
      rw [norm_inv] at h
      exact (inv_le_iff_one_le_mul₀ (norm_pos_iff.mpr (hnonzero u))).mp h
    have closedBound : IsClosed {x : X | 1 ≤ b * ‖q x‖} :=
      isClosed_le continuous_const (continuous_const.mul hq.norm)
    have contradictsZero : 1 ≤ b * ‖q p‖ := closure_minimal avoid closedBound hp
    rw [hzero, norm_zero, mul_zero] at contradictsZero
    exact (not_le_of_gt zero_lt_one) contradictsZero
  have closedH : IsClosed H := isClosed_testHull continuousTests K
  have image_closed : closure (Subtype.val '' H) = Subtype.val '' H := by
    refine Subset.antisymm ?_ subset_closure
    intro x hx
    let u : U := ⟨x, inside hx⟩
    have hu : u ∈ closure H := by
      rw [IsEmbedding.subtypeVal.closure_eq_preimage_closure_image]
      exact hx
    exact ⟨u, closedH.closure_eq ▸ hu, rfl⟩
  apply IsEmbedding.subtypeVal.isCompact_iff.mpr
  change IsCompact (Subtype.val '' H)
  rw [← image_closed]
  exact isClosed_closure.isCompact

end TransportOkaGrauert.DivisorHull
