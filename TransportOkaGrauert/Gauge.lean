import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Ring.Units
import TransportOkaGrauert.Orbits

/-! Gauge change for a left transport equation in a possibly noncommutative ring. -/
namespace TransportOkaGrauert

structure TransportOperator (R : Type*) [Ring R] where
  X : R →+ R
  leibniz : ∀ u v, X (u * v) = X u * v + u * X v

namespace TransportOperator

variable {R : Type*} [Ring R] (D : TransportOperator R)

def gauge (a : R) (f : Rˣ) : R :=
  ↑f⁻¹ * (D.X (↑f) + a * ↑f)

@[simp] theorem X_one : D.X 1 = 0 := by
  have h := D.leibniz 1 1
  simp only [mul_one, one_mul] at h
  exact (add_eq_left.mp h.symm)

@[simp] theorem gauge_one (a : R) : D.gauge a 1 = a := by simp [gauge]

theorem gauge_mul (a : R) (f g : Rˣ) :
    D.gauge a (f * g) = D.gauge (D.gauge a f) g := by
  simp only [gauge, mul_inv_rev, Units.val_mul, D.leibniz, mul_add, add_mul, mul_assoc,
    Units.inv_mul_cancel_left, add_assoc]
  exact add_left_comm _ _ _

theorem gauge_eq_zero_iff (a : R) (f : Rˣ) :
    D.gauge a f = 0 ↔ D.X ↑f + a * ↑f = 0 := by
  constructor
  · intro h
    simpa [gauge, ← mul_assoc] using congrArg (fun b : R => ↑f * b) h
  · intro h
    simp [gauge, h]

/-- Two admissible attenuations are equivalent when a permitted unit connects them.
Closure of admissible modes is unnecessary for this restricted equivalence relation. -/
def orbitSetoid (U : Set R) (G : Subgroup Rˣ) : Setoid U where
  r a b := ∃ f : G, D.gauge a.val f.val = b.val
  iseqv := {
    refl := fun a => ⟨1, D.gauge_one a.val⟩
    symm := by
      rintro a b ⟨f, hf⟩
      refine ⟨f⁻¹, ?_⟩
      rw [← hf, ← D.gauge_mul]
      simp
    trans := by
      rintro a b c ⟨f, hf⟩ ⟨g, hg⟩
      exact ⟨f * g, (D.gauge_mul a.val f.val g.val).trans (hf ▸ hg)⟩ }

/-- With orbit openness established, one obtains a permitted integrating factor. -/
theorem integratingFactor_of_open_orbits (U : Set R) (G : Subgroup Rˣ)
    [TopologicalSpace U] [PreconnectedSpace U] (hzero : (0 : R) ∈ U)
    (hopen : ∀ a, IsOpen {b | (D.orbitSetoid U G).r a b}) (a : U) :
    ∃ f : G, D.X (f.val : R) + a.val * (f.val : R) = 0 := by
  obtain ⟨f, hf⟩ := related_of_open_classes (D.orbitSetoid U G) hopen a ⟨0, hzero⟩
  exact ⟨f, (D.gauge_eq_zero_iff _ _).mp hf⟩

end TransportOperator
end TransportOkaGrauert
