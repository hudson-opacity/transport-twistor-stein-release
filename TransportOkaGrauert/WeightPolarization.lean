import TransportOkaGrauert.NearIdentity
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum

/-! For fixed geometry, a weighted cross normal is conjugate-linear in
its first weight and linear in its second. Bounded realizations of test
pairings form a complex subspace. Polarization reduces all cross normals
to the diagonal result for invertible weights. -/
namespace TransportOkaGrauert.WeightPolarization
noncomputable section
open Complex

variable {W Y : Type*} [AddCommGroup W] [Module ℂ W] [AddCommGroup Y] [Module ℂ Y]

/-- S can be the range of the map from bounded Sobolev operators to their
distributional test pairings. No self-adjointness at off-diagonal pairs of
test functions is required. -/
theorem cross_mem (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] Y) (S : Submodule ℂ Y)
    (good : W → Prop) (diagonal : ∀ x, good x → B x x ∈ S)
    (shift : ∀ w, ∃ c, good c ∧ good (c+w) ∧ good (c-w)) (u v : W) :
    B u v ∈ S := by
  have diag (w : W) : B w w ∈ S := by
    obtain ⟨c, hc, hp, hm⟩ := shift w
    have h := S.sub_mem (S.smul_mem (1/2 : ℂ)
      (S.add_mem (diagonal _ hp) (diagonal _ hm))) (diagonal _ hc)
    convert h using 1
    simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply]
    module
  have h := S.smul_mem (1/4 : ℂ)
    (S.sub_mem (S.sub_mem (diag (u+v)) (diag (u-v)))
      (S.smul_mem I (S.sub_mem (diag (u+I • v)) (diag (u-I • v)))))
  convert h using 1
  simp only [map_add, map_sub, map_smulₛₗ, LinearMap.add_apply,
    LinearMap.sub_apply, LinearMap.smul_apply, conj_I, RingHom.id_apply]
  match_scalars <;> norm_num [Complex.I_mul_I] <;> ring_nf <;> norm_num [Complex.I_sq]

open scoped Matrix.Norms.Operator

/-- Bounded matrix weights admit the three invertible shifts used in the
preceding result. The bound is a single constant for the whole patch. -/
theorem shifted_units {K : Type*} {n : ℕ} (w : K → Matrix (Fin n) (Fin n) ℂ)
    (m : ℝ) (hm : 0 ≤ m) (hb : ∀ x, ‖w x‖ ≤ m) :
    ∃ c : ℂ, IsUnit c ∧ ∀ x, IsUnit (c • 1 + w x) ∧ IsUnit (c • 1 - w x) := by
  let c : ℂ := (m+1 : ℝ)
  have hp : 0 < m+1 := by linarith
  have hn : ‖c‖ = m+1 := by exact (Complex.norm_real _).trans (abs_of_pos hp)
  have hc : c ≠ 0 := by exact Complex.ofReal_ne_zero.mpr hp.ne'
  refine ⟨c, hc.isUnit, fun x => ?_⟩
  have hsmall : ‖c⁻¹ • w x‖ < 1 := by
    rw [norm_smul, norm_inv, hn, inv_mul_lt_one₀ hp]
    exact (hb x).trans_lt (by linarith)
  have hplus : IsUnit (1 + c⁻¹ • w x) := by
    simpa using isUnit_one_sub_of_norm_lt_one (x := -(c⁻¹ • w x)) (by simpa using hsmall)
  have hminus := isUnit_one_sub_of_norm_lt_one hsmall
  have hscale : IsUnit (c • (1 : Matrix (Fin n) (Fin n) ℂ)) := by
    simpa only [Algebra.algebraMap_eq_smul_one] using hc.isUnit.map
      (algebraMap ℂ (Matrix (Fin n) (Fin n) ℂ))
  constructor
  · simpa [mul_add, smul_mul_assoc, smul_smul, hc] using hscale.mul hplus
  · simpa [mul_sub, smul_mul_assoc, smul_smul, hc] using hscale.mul hminus

end
end TransportOkaGrauert.WeightPolarization
