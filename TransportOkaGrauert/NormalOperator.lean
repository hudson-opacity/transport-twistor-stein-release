import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic

/-! The injectivity and reconstruction steps in the normal-operator argument of
Lemma 3.2. Ellipticity, regularity and the Sobolev inverse for the geometric
normal operator require independent proofs. -/
namespace TransportOkaGrauert.NormalOperator

open scoped BigOperators InnerProductSpace
noncomputable section

variable {ι H : Type*} [Fintype ι]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {K : ι → Type*} [∀ i, NormedAddCommGroup (K i)]
  [∀ i, InnerProductSpace ℂ (K i)] [∀ i, CompleteSpace (K i)]

/-- Sum of local normal operators, with localizations absorbed in Tᵢ. -/
def normal (T : ∀ i, H →L[ℂ] K i) : H →L[ℂ] H :=
  ∑ i, (T i).adjoint.comp (T i)

theorem energy (T : ∀ i, H →L[ℂ] K i) (x : H) :
    (inner ℂ (normal T x) x).re = ∑ i, ‖T i x‖ ^ 2 := by
  simp only [normal, ContinuousLinearMap.sum_apply, sum_inner, Complex.re_sum]
  exact Finset.sum_congr rfl fun i _ => ((T i).apply_norm_sq_eq_inner_adjoint_left x).symm

theorem normal_eq_zero_iff (T : ∀ i, H →L[ℂ] K i) (x : H) :
    normal T x = 0 ↔ ∀ i, T i x = 0 := by
  constructor
  · intro h i
    have he := energy T x
    simp [h] at he
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg ‖T j x‖)).mp
      he.symm i (Finset.mem_univ i)
    simpa using hz
  · intro h
    simp [normal, ContinuousLinearMap.sum_apply, h]

/-- For a partition by squares and injective local transforms, the global
normal operator is injective even though an individual cutoff has a kernel. -/
theorem localized_injective (cut : ι → H →L[ℂ] H) (I : ∀ i, H →L[ℂ] K i)
    (partition : ∀ x, ∑ i, cut i (cut i x) = x)
    (inj : ∀ i, Function.Injective (I i)) :
    Function.Injective (normal (fun i => (I i).comp (cut i))) := by
  intro x y heq
  apply sub_eq_zero.mp
  have h := (normal_eq_zero_iff (fun i => (I i).comp (cut i)) (x-y)).mp
    (by rw [map_sub, heq, sub_self])
  have hc (i : ι) : cut i (x-y) = 0 :=
    inj i ((h i).trans (map_zero (I i)).symm)
  rw [← partition (x-y)]
  simp [hc]

/-- Formula (3.5) at the level of linear maps. R restricts to the inner disk,
E extends the prescribed two modes, and the local sharp lift solves transport.
The projection identity is the localized adjoint formula (3.4). -/
theorem recover_two_modes
    {V W D B : Type*} [AddCommGroup V] [AddCommGroup W] [AddCommGroup D] [AddCommGroup B]
    (P Q : V →+ V) (E : D →+ V) (R : V →+ D)
    (trace : V →+ B) (sharp : B →+ W) (modes : W →+ D) (transport : W →+ W)
    (invert : ∀ v, P (Q v) = v) (restrict_extend : ∀ d, R (E d) = d)
    (adjoint_id : ∀ v, modes (sharp (trace v)) = R (P v))
    (homogeneous : ∀ b, transport (sharp b) = 0) :
    ∃ S : D →+ W, ∀ d, modes (S d) = d ∧ transport (S d) = 0 := by
  refine ⟨sharp.comp (trace.comp (Q.comp E)), fun d => ?_⟩
  exact ⟨(adjoint_id (Q (E d))).trans (by rw [invert, restrict_extend]), homogeneous _⟩

end
end TransportOkaGrauert.NormalOperator
