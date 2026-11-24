import TransportOkaGrauert.WeightContinuity
import TransportOkaGrauert.StableSolver

/-! Parameter stability of a finite sum of localized normal operators.
Applications use E=H² and H=H³ on the extended closed base surface.
The weighted X-ray mapping and pairing identities enter as inputs. -/
noncomputable section
namespace TransportOkaGrauert.PatchedInverse
open Set Filter Topology

variable {T W E H ι : Type*} [TopologicalSpace T] [Fintype ι]
  [AddCommGroup W] [Module ℝ W] [UniformSpace W] [IsUniformAddGroup W]
  [ContinuousSMul ℝ W] [BaireSpace W] [FirstCountableTopology W]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup H]
  [NormedSpace ℝ H] [CompleteSpace H]

/-- Patch cutoffs and the fixed angular-mode multipliers are absorbed into
the local bilinear operators. The only continuity assumptions on these
operators test smooth data and covectors in dense sets. -/
theorem local_uniform_inverse
    (N : ι → W →ₗ[ℝ] W →ₗ[ℝ] (E →L[ℝ] H))
    (weight : ι → T → W) (t : T) (hc : ∀ i, ContinuousAt (weight i) t)
    {tests : Set E} {duals : Set (H →L[ℝ] ℝ)} (ht : Dense tests) (hd : Dense duals)
    (left : ∀ i v, ∀ x ∈ tests, ∀ l ∈ duals, Continuous (fun u => l (N i u v x)))
    (right : ∀ i u, ∀ x ∈ tests, ∀ l ∈ duals, Continuous (fun v => l (N i u v x)))
    (Q : H →L[ℝ] E)
    (hQ : (∑ i, N i (weight i t) (weight i t)).comp Q = ContinuousLinearMap.id ℝ H) :
    ∃ L : T → H →L[ℝ] E, ContinuousAt L t ∧ ∀ᶠ s in 𝓝 t,
      (∑ i, N i (weight i s) (weight i s)).comp (L s) = ContinuousLinearMap.id ℝ H ∧
      ‖L s‖ < ‖Q‖ + 1 := by
  apply StableSolver.eventual_bounded_rightInverse _ t _ Q hQ
  apply tendsto_finset_sum Finset.univ
  intro i _
  exact (WeightContinuity.polarized_operatorNorm_continuous (N i) ht hd (left i)
    (right i)).2.continuousAt.comp (hc i)

end TransportOkaGrauert.PatchedInverse
