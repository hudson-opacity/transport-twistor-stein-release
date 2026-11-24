import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-! A fixed pair of Sobolev spaces can be used for each elliptic factor of a
parameter-dependent solver. A continuous family of operators with a split
surjection at the base parameter has uniformly bounded right inverses nearby.
The norm topologies on both operator spaces matter for this conclusion. -/
noncomputable section
namespace TransportOkaGrauert.StableSolver
open Filter Topology ContinuousLinearMap
variable {T E H : Type*} [TopologicalSpace T]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup H] [NormedSpace ℝ H]
  [CompleteSpace H]

/-- The Neumann correction only inverts an operator on the data space H.
E and H may be different Sobolev orders; an isomorphism E ≃ H is unnecessary. -/
theorem eventual_bounded_rightInverse (D : T → E →L[ℝ] H) (t : T)
    (hc : ContinuousAt D t) (Q : H →L[ℝ] E)
    (hQ : (D t).comp Q = ContinuousLinearMap.id ℝ H) :
    ∃ L : T → H →L[ℝ] E, ContinuousAt L t ∧
      ∀ᶠ s in 𝓝 t, (D s).comp (L s) = ContinuousLinearMap.id ℝ H ∧ ‖L s‖ < ‖Q‖ + 1 := by
  let K := fun s => (D s).comp Q
  have hK : ContinuousAt K t := hc.clm_comp continuousAt_const
  let idE := ContinuousLinearEquiv.refl ℝ H
  have hid : K t = (idE : H →L[ℝ] H) := hQ
  have hI : ContinuousAt ContinuousLinearMap.inverse (K t) := by
    rw [hid]
    exact (contDiffAt_map_inverse (n := 1) idE).continuousAt
  let L := fun s => Q.comp (K s).inverse
  have hL : ContinuousAt L t := continuousAt_const.clm_comp (hI.comp hK)
  have hLt : L t = Q := by
    change Q.comp (K t).inverse = Q
    rw [hid, inverse_equiv]
    rfl
  have hbound : ∀ᶠ s in 𝓝 t, ‖L s‖ < ‖Q‖ + 1 :=
    hL.norm.eventually_lt_const (by change ‖L t‖ < _; rw [hLt]; linarith)
  have hopen : {p : H →L[ℝ] H | p.IsInvertible} ∈ 𝓝 (K t) := by
    rw [hid]
    exact idE.nhds
  refine ⟨L, hL, ?_⟩
  filter_upwards [hK.tendsto hopen, hbound] with s hi hb
  refine ⟨?_, hb⟩
  obtain ⟨e, he⟩ : (K s).IsInvertible := hi
  change (D s).comp (Q.comp (K s).inverse) = _
  rw [← ContinuousLinearMap.comp_assoc]
  change (K s).comp (K s).inverse = _
  rw [← he, inverse_equiv]
  ext x
  exact e.apply_symm_apply x

end TransportOkaGrauert.StableSolver
