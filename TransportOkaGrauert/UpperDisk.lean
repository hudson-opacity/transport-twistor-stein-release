import TransportOkaGrauert.BoundaryModes
import TransportOkaGrauert.PolynomialDisk
import TransportOkaGrauert.UpperRecursion
import TransportOkaGrauert.Nilpotent

/-! Arbitrary rank, base-dependent polynomial coefficients, and noncommuting values.
The ordered integrations terminate by strict upper triangularity. -/
namespace TransportOkaGrauert.UpperDisk

noncomputable section
open scoped ComplexConjugate ContDiff
open FlatScalar PolynomialDisk Nilpotent BoundaryModes
local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ
variable {n : ℕ}

abbrev Coefficients (n : ℕ) := Fin n → Fin n → List Monomial

def field (a : Coefficients n) (z w : ℂ) : Mat n :=
  fun i j => if i < j then eval (a i j) z w else 0

def terms (a : Coefficients n) (i j : Fin n) := expand (a i j)

theorem field_eq (a : Coefficients n) (z w : ℂ) (i j : Fin n) :
    field a z w i j = attenuation (upperTerms (terms a) i j) z w := by
  by_cases h : i < j
  · simp [field, upperTerms, h, terms, expand_spec]
  · simp [field, upperTerms, h, attenuation]

def increment (a : Coefficients n) (z w : ℂ) : Mat n :=
  fun i j => -primitive (upperP (terms a) i j) z w

def frame (a : Coefficients n) (z w : ℂ) : Mat n := 1 + increment a z w

def inverseFrame (a : Coefficients n) (z w : ℂ) : Mat n := finiteInverse (increment a z w)

theorem inverse_identities (a : Coefficients n) (z w : ℂ) :
    frame a z w * inverseFrame a z w = 1 ∧ inverseFrame a z w * frame a z w = 1 := by
  apply finiteInverse_spec
  intro i j h
  simp [increment, upperP_eq_nil _ _ _ h, primitive]

theorem geodesic_transport (a : Coefficients n) (z w : ℂ) (hw : w * conj w = 1)
    (i j : Fin n) :
    HasDerivAt (fun t : ℝ => frame a (z + t * w) w i j) (-(field a z w * frame a z w) i j) 0 := by
  have h := ((transport (upperP (terms a) i j) z w hw).neg).const_add ((1 : Mat n) i j)
  convert h using 1
  rw [upperP_attenuation, frame, mul_add, mul_one, Matrix.add_apply, Matrix.mul_apply]
  simp [increment, field_eq, Finset.sum_neg_distrib, sub_eq_add_neg]

theorem field_modes (a : Coefficients n) (z : ℂ) (i j : Fin n) (k : ℤ) (hk : k < -1) :
    fourierCoeff (boundaryTrace (fun w => field a z w i j)) k = 0 := by
  simpa only [field_eq] using
    scalar_attenuation (upperTerms (terms a) i j) z k hk

theorem regularity (a : Coefficients n) (i j : Fin n) :
    ContDiff ℝ ∞ (fun p : ℂ × ℂ => frame a p.1 p.2 i j) ∧
    ContDiff ℝ ∞ (fun p : ℂ × ℂ => inverseFrame a p.1 p.2 i j) ∧
    ∀ z, Differentiable ℂ (fun w => frame a z w i j) ∧
      Differentiable ℂ (fun w => inverseFrame a z w i j) := by
  have hs (k l : Fin n) := (primitive_smooth (upperP (terms a) k l)).neg
  have hd (z : ℂ) (k l : Fin n) := (primitive_entire (upperP (terms a) k l) z).neg
  exact ⟨contDiff_const.add (hs i j),
    finiteInverse_smooth (fun p => increment a p.1 p.2) hs i j,
    fun z => ⟨(differentiable_const _).add (hd z i j),
      finiteInverse_differentiable (increment a z) (hd z) i j⟩⟩

/-- The two matrices belong to the holomorphic gauge group on the boundary
circle, expressed with normalized Haar Fourier coefficients. -/
theorem frame_modes (a : Coefficients n) (z : ℂ) (i j : Fin n) (k : ℤ) (hk : k < 0) :
    fourierCoeff (boundaryTrace (fun w => frame a z w i j)) k = 0 ∧
    fourierCoeff (boundaryTrace (fun w => inverseFrame a z w i j)) k = 0 := by
  obtain ⟨hf, hg⟩ := (regularity a i j).2.2 z
  exact ⟨negativeMode_eq_zero hf.diffContOnCl k hk, negativeMode_eq_zero hg.diffContOnCl k hk⟩

/-- The transport formulation on the Euclidean disk. Smoothness here is
witnessed by global smooth functions on the ambient base and velocity planes. -/
def IsHolomorphicIntegratingFactor (A F G : ℂ → ℂ → Mat n) : Prop :=
  (∀ i j, ContDiff ℝ ∞ (fun p : ℂ × ℂ => F p.1 p.2 i j) ∧
    ContDiff ℝ ∞ (fun p : ℂ × ℂ => G p.1 p.2 i j)) ∧
  (∀ z w, F z w * G z w = 1 ∧ G z w * F z w = 1) ∧
  (∀ z i j k, k < 0 →
    fourierCoeff (boundaryTrace (fun w => F z w i j)) k = 0 ∧
    fourierCoeff (boundaryTrace (fun w => G z w i j)) k = 0) ∧
  ∀ z w, w * conj w = 1 → ∀ i j, HasDerivAt (fun t : ℝ => F (z + t * w) w i j)
    (-(A z w * F z w) i j) 0

/-- Every strictly upper triangular polynomial attenuation in the stated
ordinary coordinates admits smooth holomorphic integrating factors in every rank. -/
theorem polynomial_integrating_factor (a : Coefficients n) :
    ∃ F G, IsHolomorphicIntegratingFactor (field a) F G :=
  ⟨frame a, inverseFrame a,
    fun i j => ⟨(regularity a i j).1, (regularity a i j).2.1⟩,
    inverse_identities a, frame_modes a, geodesic_transport a⟩

end
end TransportOkaGrauert.UpperDisk
