import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Data.NNReal.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

/-!
# The Fourier correction in Proposition 3.1

For a skew-Hermitian pair the attenuated geodesic derivative is tridiagonal
in the circle modes. Given the three solvers of Lemmas 3.2–3.4 of
Bohr–Paternain, we construct the linear right inverse on the holomorphic
sector and track its loss of one Sobolev derivative.

A common coefficient space `E` can be used in a circle trivialization.
The submodule `S` specifies which complete sequences are admissible
(e.g. Fourier coefficients of smooth fields). No convergence or decay of
arbitrary sequences is presumed.
-/

namespace TransportOkaGrauert.RightInverse

open scoped NNReal

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]

/-- The three entries are indexed by the *input* frequency. -/
structure Transport (K E : Type*) [Field K] [AddCommGroup E] [Module K E] where
  raise : ℤ → E →ₗ[K] E
  stay : ℤ → E →ₗ[K] E
  lower : ℤ → E →ₗ[K] E

/-- Fourier-coordinate formula for `X+A` with a connection and Higgs field. -/
def Transport.apply (D : Transport K E) (u : ℤ → E) (k : ℤ) : E :=
  D.raise (k - 1) (u (k - 1)) + D.stay k (u k) + D.lower (k + 1) (u (k + 1))

/-- Orthogonal Fourier projection in coordinates. -/
def project (m : ℤ) : (ℤ → E) →ₗ[K] (ℤ → E) where
  toFun u k := if m ≤ k then u k else 0
  map_add' _ _ := by ext k; by_cases h : m ≤ k <;> simp [h]
  map_smul' _ _ := by ext k; by_cases h : m ≤ k <;> simp [h]

@[simp] theorem project_apply (m : ℤ) (u : ℤ → E) (k : ℤ) :
    project (K := K) m u k = if m ≤ k then u k else 0 := rfl

/-- An admissible coefficient sequence supported in frequencies ≥ `m`. -/
def sector (S : Submodule K (ℤ → E)) (m : ℤ) : Submodule K S where
  carrier := {u | ∀ k < m, (u : ℤ → E) k = 0}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy k hk; simp [hx k hk, hy k hk]
  smul_mem' := by intro c x hx k hk; simp [hx k hk]

/-- Lemma 3.4 supplies `solve`, Lemma 3.3 supplies `liftLower` and
`liftRaise`, and Lemma 3.2 supplies `extend` with prescribed adjacent
modes. Appendix Lemma 6.1 supplies invariance under positive projection. -/
structure Solvers (D : Transport K E) (S : Submodule K (ℤ → E)) where
  project_mem : ∀ u : S, project (K := K) 0 u.val ∈ S
  solve : S →ₗ[K] S
  solve_eq : ∀ f, D.apply (solve f).val = f.val
  liftLower : E →ₗ[K] E
  liftLower_eq : ∀ q, D.lower 0 (liftLower q) = q
  liftRaise : E →ₗ[K] E
  liftRaise_eq : ∀ q, D.raise (-1) (liftRaise q) = q
  extend : E × E →ₗ[K] S
  extend_eq : ∀ g, D.apply (extend g).val = 0
  extend_negOne : ∀ g, (extend g).val (-1) = g.1
  extend_zero : ∀ g, (extend g).val 0 = g.2

namespace Solvers

variable {D : Transport K E} {S : Submodule K (ℤ → E)} (H : Solvers D S)

/-- The positive projection as an endomorphism of admissible fields. -/
def positive : S →ₗ[K] S :=
  ((project (K := K) 0).comp S.subtype).codRestrict S H.project_mem

/-- The only discarded terms, in target modes −1 and 0 respectively. -/
def defect (D : Transport K E) (S : Submodule K (ℤ → E)) : S →ₗ[K] E × E where
  toFun u := (D.stay (-1) (u.val (-1)) + D.raise (-2) (u.val (-2)),
    D.raise (-1) (u.val (-1)))
  map_add' _ _ := by ext <;> (simp; try abel)
  map_smul' _ _ := by ext <;> simp [smul_add]

/-- Required source modes `(g₋₁,g₀)` for the homogeneous correction. -/
def lift : E × E →ₗ[K] E × E :=
  ((-H.liftRaise).comp (LinearMap.snd K E E)).prod
    (H.liftLower.comp (LinearMap.fst K E E))

/-- The unrestricted solution plus its homogeneous correction, both truncated
to the holomorphic sector. -/
def corrected : S →ₗ[K] S :=
  H.positive.comp H.solve +
    H.positive.comp (H.extend.comp (H.lift.comp ((defect D S).comp H.solve)))

private theorem corrected_val (f : S) (k : ℤ) :
    (H.corrected f).val k = project (K := K) 0 (H.solve f).val k +
      project (K := K) 0 (H.extend (H.lift (defect D S (H.solve f)))).val k := rfl

/-- Every coefficient with negative frequency vanishes. -/
theorem corrected_mem (f : S) : H.corrected f ∈ sector S 0 := by
  intro k hk
  simp [H.corrected_val, not_le.mpr hk]

/-- Actual linear operator between the frequency-restricted spaces. -/
def holomorphicRightInverse : sector S (-1) →ₗ[K] sector S 0 :=
  (H.corrected.comp (sector S (-1)).subtype).codRestrict (sector S 0)
    (fun f => H.corrected_mem f.val)

/-- The tridiagonal formula leaves only two exceptional frequencies.
At frequency −1 the homogeneous correction adds `μ₋g₀`, and at frequency
0 it subtracts `μ₊g₋₁`. -/
theorem solve_holomorphic (f : sector S (-1)) :
    D.apply (H.holomorphicRightInverse f).val.val = f.val.val := by
  let u := H.solve f.val
  let q := defect D S u
  let v := H.extend (H.lift q)
  have hu (j : ℤ) : D.apply u.val j = f.val.val j := congrFun (H.solve_eq f.val) j
  have hv (j : ℤ) : D.apply v.val j = 0 := congrFun (H.extend_eq (H.lift q)) j
  have hv₀ : D.lower 0 (v.val 0) = q.1 := by
    change D.lower 0 ((H.extend (H.lift q)).val 0) = q.1
    rw [H.extend_zero]
    exact H.liftLower_eq q.1
  have hv₁ : D.raise (-1) (v.val (-1)) = -q.2 := by
    change D.raise (-1) ((H.extend (H.lift q)).val (-1)) = -q.2
    rw [H.extend_negOne]
    change D.raise (-1) (-H.liftRaise q.2) = -q.2
    rw [map_neg, H.liftRaise_eq]
  funext k
  change D.apply (H.corrected f.val).val k = f.val.val k
  by_cases hneg : k < -1
  · rw [f.property k hneg]
    simp only [Transport.apply, H.corrected_val, project_apply]
    simp [show ¬ 1 ≤ k by omega, show ¬ 0 ≤ k by omega, show ¬ 0 ≤ k + 1 by omega]
  by_cases hminus : k = -1
  · subst k
    have he := hu (-1)
    norm_num [Transport.apply] at he
    change D.lower 0 (v.val 0) = D.stay (-1) (u.val (-1)) + D.raise (-2) (u.val (-2)) at hv₀
    simp only [Transport.apply, H.corrected_val, project_apply]
    norm_num
    change D.lower 0 (u.val 0) + D.lower 0 (v.val 0) = _
    rw [hv₀, ← he]
    abel
  by_cases hzero : k = 0
  · subst k
    have he := hu 0
    have hhom := hv 0
    norm_num [Transport.apply] at he hhom
    change D.raise (-1) (v.val (-1)) = -(D.raise (-1) (u.val (-1))) at hv₁
    rw [hv₁] at hhom
    simp only [Transport.apply, H.corrected_val, project_apply]
    norm_num
    change D.stay 0 (u.val 0) + D.stay 0 (v.val 0) +
      (D.lower 1 (u.val 1) + D.lower 1 (v.val 1)) = _
    have hc : D.stay 0 (v.val 0) + D.lower 1 (v.val 1) = D.raise (-1) (u.val (-1)) := by
      apply sub_eq_zero.mp
      rw [← hhom]
      abel
    rw [← he, ← hc]
    abel
  · have he := hu k
    have hhom := hv k
    simp only [Transport.apply, H.corrected_val, project_apply]
    simp only [if_pos (show 0 ≤ k - 1 by omega), if_pos (show 0 ≤ k by omega),
      if_pos (show 0 ≤ k + 1 by omega), map_add]
    change D.raise (k - 1) (u.val (k - 1)) + D.raise (k - 1) (v.val (k - 1)) +
      (D.stay k (u.val k) + D.stay k (v.val k)) +
      (D.lower (k + 1) (u.val (k + 1)) + D.lower (k + 1) (v.val (k + 1))) = _
    rw [← he, ← add_zero (D.apply u.val k), ← hhom]
    unfold Transport.apply
    abel

/-- The individual estimates used for the tame bound in Proposition 3.1.
The cost of prescribing two modes in `extend` is offset by the one
derivative gained by the elliptic one-mode solvers in `lift`. -/
structure SobolevBounds (H : Solvers D S)
    (fieldSize : ℕ → S → ℝ≥0) (pairSize : ℕ → E × E → ℝ≥0) where
  Cproject : ℕ → ℝ≥0
  Csolve : ℕ → ℝ≥0
  Cdefect : ℕ → ℝ≥0
  Clift : ℕ → ℝ≥0
  Cextend : ℕ → ℝ≥0
  triangle : ∀ s u v, fieldSize s (u + v) ≤ fieldSize s u + fieldSize s v
  mono : ∀ s f, fieldSize s f ≤ fieldSize (s + 1) f
  project_bound : ∀ s u, fieldSize s (H.positive u) ≤ Cproject s * fieldSize s u
  solve_bound : ∀ s f, fieldSize s (H.solve f) ≤ Csolve s * fieldSize s f
  defect_bound : ∀ s u, pairSize s (defect D S u) ≤ Cdefect s * fieldSize (s + 1) u
  lift_bound : ∀ s q, pairSize (s + 1) (H.lift q) ≤ Clift s * pairSize s q
  extend_bound : ∀ s g, fieldSize s (H.extend g) ≤ Cextend s * pairSize (s + 1) g

/-- The explicitly constructed linear right inverse is tame of degree one.
The constant depends on the degree and the solvers, independently of `f`. -/
theorem tame_rightInverse {N : ℕ → S → ℝ≥0} {P : ℕ → E × E → ℝ≥0}
    (B : SobolevBounds H N P) (s : ℕ) :
    ∃ C : ℝ≥0, ∀ f : sector S (-1),
      N s (H.holomorphicRightInverse f).val ≤ C * N (s + 1) f.val := by
  refine ⟨B.Cproject s * (B.Csolve s +
    B.Cextend s * B.Clift s * B.Cdefect s * B.Csolve (s + 1)), ?_⟩
  intro f
  let u := H.solve f.val
  let q := defect D S u
  let g := H.lift q
  let v := H.extend g
  have hu : N s u ≤ B.Csolve s * N (s + 1) f.val := by
    exact (B.solve_bound s f.val).trans (mul_le_mul_right (B.mono s f.val) _)
  have hq : P s q ≤ B.Cdefect s * (B.Csolve (s + 1) * N (s + 1) f.val) :=
    (B.defect_bound s u).trans (mul_le_mul_right (B.solve_bound (s + 1) f.val) _)
  have hg := (B.lift_bound s q).trans (mul_le_mul_right hq _)
  have hv := (B.extend_bound s g).trans (mul_le_mul_right hg _)
  change N s (H.positive u + H.positive v) ≤ _
  calc
    _ ≤ N s (H.positive u) + N s (H.positive v) := B.triangle s _ _
    _ ≤ B.Cproject s * (B.Csolve s * N (s + 1) f.val) +
        B.Cproject s * (B.Cextend s * (B.Clift s *
          (B.Cdefect s * (B.Csolve (s + 1) * N (s + 1) f.val)))) :=
      add_le_add ((B.project_bound s u).trans (mul_le_mul_right hu _))
        ((B.project_bound s v).trans (mul_le_mul_right hv _))
    _ = _ := by ring

end Solvers

end TransportOkaGrauert.RightInverse
