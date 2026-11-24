import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Fourier.AddCircle
import TransportOkaGrauert.Triangular

/-!
# Fourier modes of boundary values on the velocity disk

The negative modes of a disk-holomorphic function vanish by the Cauchy
integral theorem, including when the function is merely continuous on the
boundary. The functions below are evaluated on the additive circle of angles
with period `2π`, using mathlib's normalized Haar Fourier coefficients.
-/

namespace TransportOkaGrauert.BoundaryModes

open AddCircle Complex Metric Real
open scoped Real ComplexConjugate Matrix

noncomputable section

local instance : Fact (0 < 2 * π) := ⟨Real.two_pi_pos⟩

/-- Boundary value on the unit circle in the fiber plane. -/
def boundaryTrace {E : Type*} (f : ℂ → E) (θ : AddCircle (2 * π)) : E := f θ.toCircle

private theorem velocity_at_angle (t : ℝ) :
    (AddCircle.toCircle (t : AddCircle (2 * π)) : ℂ) = circleMap 0 1 t := by
  simp [AddCircle.toCircle, circleMap]

private theorem positive_fourier_weight (k : ℕ) (t : ℝ) :
    fourier (k : ℤ) (t : AddCircle (2 * π)) = circleMap 0 1 t ^ k := by
  rw [← velocity_at_angle t]
  simp [AddCircle.toCircle_nsmul]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A holomorphic function on the open unit disk that is continuous on its
closure has no negative Fourier modes in its boundary values. -/
theorem negativeMode_eq_zero {f : ℂ → E} (hf : DiffContOnCl ℂ f (ball 0 1))
    (n : ℤ) (hn : n < 0) : fourierCoeff (boundaryTrace f) n = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = -((k + 1 : ℕ) : ℤ) := ⟨(-n - 1).toNat, by omega⟩
  have hpow : Differentiable ℂ (fun z : ℂ => z ^ k) := differentiable_id.pow k
  have hc := (hpow.diffContOnCl.smul hf).circleIntegral_eq_zero (by norm_num : (0 : ℝ) ≤ 1)
  have hcircle :
      (∮ z in C(0, 1), z ^ k • f z) =
      I • ∫ t : ℝ in 0..2 * π, circleMap 0 1 t ^ (k + 1) • f (circleMap 0 1 t) := by
    rw [circleIntegral, ← intervalIntegral.integral_smul]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    rw [deriv_circleMap, smul_smul, smul_smul, pow_succ]
    congr 1
    ring
  rw [hcircle] at hc
  have hz := (smul_eq_zero.mp hc).resolve_left I_ne_zero
  rw [fourierCoeff_eq_intervalIntegral _ _ 0, zero_add, neg_neg]
  simp only [positive_fourier_weight, boundaryTrace, velocity_at_angle, hz, smul_zero]

/-- Both factors in the flat scalar construction satisfy the Fourier condition
used in the transport gauge group. -/
theorem scalar_factors (terms : List FlatScalar.Term) (z : ℂ) (n : ℤ) (hn : n < 0) :
    fourierCoeff (boundaryTrace (FlatScalar.factor terms z)) n = 0 ∧
    fourierCoeff (boundaryTrace (FlatScalar.inverseFactor terms z)) n = 0 := by
  obtain ⟨hf, hi, _⟩ := FlatScalar.flatScalarIntegratingFactor terms z
  exact ⟨negativeMode_eq_zero hf.diffContOnCl n hn, negativeMode_eq_zero hi.diffContOnCl n hn⟩

/-- Entrywise application to a rank-three, possibly noncommuting attenuation. -/
theorem triangular_factors (a b c : List FlatScalar.Term) (z : ℂ) (i j : Fin 3)
    (n : ℤ) (hn : n < 0) :
    fourierCoeff (boundaryTrace (fun w => FlatScalar.triangularF a b c z w i j)) n = 0 ∧
    fourierCoeff (boundaryTrace (fun w => FlatScalar.triangularInverse a b c z w i j)) n = 0 := by
  obtain ⟨hf, hi⟩ := FlatScalar.triangular_entire a b c z i j
  exact ⟨negativeMode_eq_zero hf.diffContOnCl n hn, negativeMode_eq_zero hi.diffContOnCl n hn⟩

/-- Multiplication by the conjugate unit direction shifts every Fourier mode
down by one. -/
theorem conjugate_shift (f : AddCircle (2 * π) → ℂ) (n : ℤ) :
    fourierCoeff (fun θ => conj (θ.toCircle : ℂ) * f θ) n = fourierCoeff f (n + 1) := by
  have weight (θ : AddCircle (2 * π)) :
      fourier (-(n + 1)) θ = fourier (-n) θ * conj (θ.toCircle : ℂ) := by
    rw [neg_add, fourier_add, fourier_neg (n := 1), fourier_one]
  simp only [fourierCoeff, weight, smul_eq_mul, mul_assoc]

/-- Removing the single conjugate velocity factor from the flat attenuation
leaves a polynomial on the full velocity plane. -/
def numerator (terms : List FlatScalar.Term) (z w : ℂ) : ℂ :=
  (terms.map (fun m => m.coeff z w * conj z ^ m.q)).sum

theorem attenuation_split (terms : List FlatScalar.Term) (z w : ℂ) :
    FlatScalar.attenuation terms z w = conj w * numerator terms z w := by
  induction terms with
  | nil => simp [FlatScalar.attenuation, numerator]
  | cons m l ih =>
    change m.attenuation z w + FlatScalar.attenuation l z w =
      conj w * (m.coeff z w * conj z ^ m.q + numerator l z w)
    rw [ih, FlatScalar.Term.attenuation]
    ring

theorem numerator_entire (terms : List FlatScalar.Term) (z : ℂ) :
    Differentiable ℂ (numerator terms z) := by
  induction terms with
  | nil => exact differentiable_const _
  | cons m l ih =>
    change Differentiable ℂ (fun w => m.coeff z w * conj z ^ m.q + numerator l z w)
    apply Differentiable.add _ ih
    unfold FlatScalar.Term.coeff FlatScalar.firstIntegral
    fun_prop

/-- The flat scalar attenuations obey the paper's admissibility cutoff. -/
theorem scalar_attenuation (terms : List FlatScalar.Term) (z : ℂ) (n : ℤ) (hn : n < -1) :
    fourierCoeff (boundaryTrace (FlatScalar.attenuation terms z)) n = 0 := by
  change fourierCoeff (fun θ => FlatScalar.attenuation terms z θ.toCircle) n = 0
  simp only [attenuation_split]
  rw [conjugate_shift]
  exact negativeMode_eq_zero (numerator_entire terms z).diffContOnCl _ (by omega)

/-- The same cutoff holds independently in every matrix entry. -/
theorem triangular_attenuation (a b c : List FlatScalar.Term) (z : ℂ) (i j : Fin 3)
    (n : ℤ) (hn : n < -1) :
    fourierCoeff (boundaryTrace (fun w => FlatScalar.triangularA a b c z w i j)) n = 0 := by
  fin_cases i <;> fin_cases j <;> simp [FlatScalar.triangularA] <;>
    first | exact scalar_attenuation _ _ _ hn | simp [fourierCoeff, boundaryTrace]

end
end TransportOkaGrauert.BoundaryModes
