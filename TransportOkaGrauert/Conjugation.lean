import TransportOkaGrauert.Gauge
import Mathlib.Data.NNReal.Basic
import Mathlib.Tactic.NoncommRing

/-! Conjugating the right inverse, the last step of Proposition 3.1. -/
namespace TransportOkaGrauert.TransportOperator

variable {R : Type*} [Ring R] (D : TransportOperator R)

def covariant (a u : R) := D.X u + a * u

/-- The commutator linearization is itself a derivation of the ring of matrices. -/
def adjointConnection (a : R) : TransportOperator R where
  X := D.X + AddMonoidHom.mulLeft a - AddMonoidHom.mulRight a
  leibniz x y := by
    change D.X (x*y) + a*(x*y) - (x*y)*a =
      (D.X x + a*x - x*a)*y + x*(D.X y + a*y - y*a)
    rw [D.leibniz]
    noncomm_ring

theorem intertwine (a : R) (f : Rˣ) (v : R) :
    D.covariant a (↑f * v) = ↑f * D.covariant (D.gauge a f) v := by
  simp only [covariant, gauge, D.leibniz, mul_add, add_mul, mul_assoc,
    Units.mul_inv_cancel_left]
  rw [add_assoc, add_left_comm]

/-- An additive solver is transformed by Lₐh = F Lᵦ(F⁻¹h).
The domain may be restricted by a lower Fourier-mode bound. -/
def conjugateSolver (f : Rˣ) (L : R →+ R) : R →+ R :=
  (AddMonoidHom.mulLeft (↑f : R)).comp (L.comp (AddMonoidHom.mulLeft (↑f⁻¹ : R)))

theorem conjugateSolver_rightInverse (a : R) (f : Rˣ) (L : R →+ R)
    (rhs holo : Set R)
    (domain : ∀ h ∈ rhs, (↑f⁻¹ : R) * h ∈ rhs)
    (range : ∀ u ∈ holo, (↑f : R) * u ∈ holo)
    (solve : ∀ h ∈ rhs, L h ∈ holo ∧ D.covariant (D.gauge a f) (L h) = h)
    (h : R) (hh : h ∈ rhs) :
    conjugateSolver f L h ∈ holo ∧ D.covariant a (conjugateSolver f L h) = h := by
  obtain ⟨hmem, heq⟩ := solve _ (domain _ hh)
  refine ⟨range _ hmem, ?_⟩
  change D.covariant a (↑f * L (↑f⁻¹ * h)) = h
  rw [D.intertwine, heq, Units.mul_inv_cancel_left]

/-- Fixed smooth gauge multipliers with degree-zero bounds preserve a solver's
loss of d derivatives. Constants may depend on the Sobolev index. -/
theorem conjugateSolver_bound (f : Rˣ) (L : R →+ R) (p : ℕ → R → NNReal)
    (A B C : ℕ → NNReal) (d s : ℕ) (h : R)
    (forward : ∀ u, p s ((↑f : R) * u) ≤ A s * p s u)
    (backward : p (s+d) ((↑f⁻¹ : R) * h) ≤ B (s+d) * p (s+d) h)
    (solver : ∀ v, p s (L v) ≤ C s * p (s+d) v) :
    p s (conjugateSolver f L h) ≤ (A s * C s * B (s+d)) * p (s+d) h := by
  calc
    _ ≤ A s * p s (L ((↑f⁻¹ : R) * h)) := forward _
    _ ≤ A s * (C s * p (s+d) ((↑f⁻¹ : R) * h)) := mul_le_mul_right (solver _) _
    _ ≤ A s * (C s * (B (s+d) * p (s+d) h)) :=
      mul_le_mul_right (mul_le_mul_right backward _) _
    _ = _ := by simp [mul_assoc]

end TransportOkaGrauert.TransportOperator
