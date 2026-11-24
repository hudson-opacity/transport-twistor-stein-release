import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Tactic

/-! # Closed range for an injective compact perturbation of the identity

The minimum below is taken on the compact image of the closed unit ball.
This gives a quantitative estimate without using a spectral theorem.
For a self-adjoint perturbation the estimate gives surjectivity. -/
namespace TransportOkaGrauert.NormalFredholm
noncomputable section
open Set Metric
open scoped RealInnerProductSpace

theorem bounded_below {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : E →L[ℝ] E)
    (compact : ∃ C : Set E, IsCompact C ∧ K '' closedBall 0 1 ⊆ C)
    (inj : Function.Injective (ContinuousLinearMap.id ℝ E + K)) :
    ∃ c : ℝ, 0 < c ∧ ∀ x, c * ‖x‖ ≤ ‖(ContinuousLinearMap.id ℝ E + K) x‖ := by
  let T := ContinuousLinearMap.id ℝ E + K
  obtain ⟨C,hC,image⟩ := compact
  let g (z : E) := ‖T z‖ + |1 - ‖z‖|
  have hg : Continuous g := T.continuous.norm.add (continuous_const.sub continuous_norm).abs
  have pos (z : E) : 0 < g z := by
    by_cases h : T z = 0
    · have e : z = 0 := inj (h.trans (map_zero T).symm)
      simp [e,g]
    · exact add_pos_of_pos_of_nonneg (norm_pos_iff.mpr h) (abs_nonneg _)
  obtain ⟨m,hm,hmin⟩ := hC.exists_forall_le' hg.continuousOn (a := 0) (fun z _ => pos z)
  have den : 0 < ‖K‖ + 1 := by positivity
  let c := m / (‖K‖ + 1)
  have sphere (u : E) (hu : ‖u‖ = 1) : c ≤ ‖T u‖ := by
    have h := hmin (K u) (image ⟨u,mem_closedBall_zero_iff.mpr hu.le,rfl⟩)
    have a : T (K u) = K (T u) := by simp [T]
    have b : |1 - ‖K u‖| ≤ ‖T u‖ := by
      have d := abs_norm_sub_norm_le u (-(K u))
      simpa [T,norm_neg,hu] using d
    change m ≤ ‖T (K u)‖ + |1 - ‖K u‖| at h
    rw [a] at h
    apply (div_le_iff₀ den).mpr
    nlinarith [K.le_opNorm (T u)]
  refine ⟨c,div_pos hm den,fun x => ?_⟩
  change c * ‖x‖ ≤ ‖T x‖
  by_cases zero : x = 0
  · simp [zero]
  have hx := norm_pos_iff.mpr zero
  have s : ‖(‖x‖⁻¹ : ℝ) • x‖ = 1 := by
    rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hx.le),inv_mul_cancel₀ hx.ne']
  have small := sphere _ s
  rw [map_smul,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hx.le),←div_eq_inv_mul] at small
  exact (le_div_iff₀ hx).mp small

/-- Self-adjoint injective compact perturbations of the identity on a real
Hilbert space have full range. The compact hypothesis is the image-of-ball
form, directly suited to a norm limit of smooth off-diagonal kernels. -/
theorem surjective {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (K : E →L[ℝ] E)
    (compact : ∃ C : Set E, IsCompact C ∧ K '' closedBall 0 1 ⊆ C)
    (inj : Function.Injective (ContinuousLinearMap.id ℝ E + K))
    (self : ContinuousLinearMap.adjoint (ContinuousLinearMap.id ℝ E + K) = ContinuousLinearMap.id ℝ E + K) :
    Function.Surjective (ContinuousLinearMap.id ℝ E + K) := by
  let T := ContinuousLinearMap.id ℝ E + K
  obtain ⟨c,hc,below⟩ := bounded_below K compact inj
  have anti : AntilipschitzWith (Real.toNNReal c⁻¹) T := by
    apply T.antilipschitz_of_bound
    intro x
    rw [Real.coe_toNNReal _ (inv_nonneg.mpr hc.le),←div_eq_inv_mul,le_div_iff₀ hc,mul_comm]
    exact below x
  have closed : IsClosed (T.range : Set E) := anti.isClosed_range T.uniformContinuous
  haveI := closed.completeSpace_coe
  apply LinearMap.range_eq_top.mp
  apply T.range.orthogonal_eq_bot_iff.mp
  rw [T.orthogonal_range,show T.adjoint = T from self,LinearMap.ker_eq_bot]
  exact inj

end
end TransportOkaGrauert.NormalFredholm
