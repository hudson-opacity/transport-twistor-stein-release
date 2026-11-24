import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Real.Basic

/-!
# A finite obstruction to strict convexity on a balanced net

At a vertex, the outgoing vectors have a positive weighted sum equal to zero.
A linear functional must be nonnegative on at least one of those vectors.
At a vertex maximizing a proposed potential, this contradicts the strict
first-order convexity inequality along that edge.

The vectors may belong to a different real vector space at each vertex. In
the geometric application, they are initial velocities of edges parametrized
on the unit interval. Given a balanced net, the theorem produces an edge on
which the strict inequality fails.
-/

namespace TransportOkaGrauert.RigidityNet

open scoped BigOperators

/-- A positive linear dependence prevents every outgoing slope from being negative. -/
theorem exists_nonnegative_slope {ι T : Type*} [AddCommMonoid T] [Module ℝ T]
    (edges : Finset ι) (nonempty : edges.Nonempty) (weight : ι → ℝ) (velocity : ι → T)
    (positive : ∀ e ∈ edges, 0 < weight e)
    (balance : ∑ e ∈ edges, weight e • velocity e = 0) (slope : T →ₗ[ℝ] ℝ) :
    ∃ e ∈ edges, 0 ≤ slope (velocity e) := by
  by_contra h
  have hneg : ∀ e ∈ edges, weight e * slope (velocity e) < 0 := by
    intro e he
    exact mul_neg_of_pos_of_neg (positive e he) (lt_of_not_ge fun hs => h ⟨e, he, hs⟩)
  have hs : (∑ e ∈ edges, weight e * slope (velocity e)) < ∑ _e ∈ edges, (0 : ℝ) :=
    Finset.sum_lt_sum_of_nonempty nonempty hneg
  have hz : (∑ e ∈ edges, weight e * slope (velocity e)) = 0 := by
    simpa only [map_sum, map_smul, smul_eq_mul, map_zero] using congrArg slope balance
  simp [hz] at hs

/-- Some outgoing edge fails strict first-order convexity for any choice of vertex
values and linear differentials on a finite nonempty closed balanced net. -/
theorem exists_edge_violating_strict_convexity {V : Type*} [Fintype V] [Nonempty V]
    {T : V → Type*} [∀ v, AddCommMonoid (T v)] [∀ v, Module ℝ (T v)]
    (neighbors : V → Finset V) (nonempty : ∀ v, (neighbors v).Nonempty)
    (weight : V → V → ℝ) (velocity : (v : V) → V → T v)
    (positive : ∀ v w, w ∈ neighbors v → 0 < weight v w)
    (balance : ∀ v, ∑ w ∈ neighbors v, weight v w • velocity v w = 0)
    (value : V → ℝ) (slope : (v : V) → T v →ₗ[ℝ] ℝ) :
    ∃ v w, w ∈ neighbors v ∧ value w - value v ≤ slope v (velocity v w) := by
  classical
  obtain ⟨v, _, hmax⟩ := Finset.exists_max_image Finset.univ value Finset.univ_nonempty
  obtain ⟨w, hw, hs⟩ := exists_nonnegative_slope (neighbors v) (nonempty v) (weight v)
    (velocity v) (positive v) (balance v) (slope v)
  exact ⟨v, w, hw, (sub_nonpos.mpr (hmax w (Finset.mem_univ w))).trans hs⟩

end TransportOkaGrauert.RigidityNet
