import Mathlib.Algebra.DualNumber
import TransportOkaGrauert.Gauge

/-!
# First variation of the transport gauge action

We extend a derivation to the dual numbers by fixing the infinitesimal
parameter. The coefficient of that parameter in the action of `1 + εH`
is precisely the operator in Bohr–Paternain, equation (3.1). This is an
identity in the square-zero extension of an arbitrary associative ring.
-/

namespace TransportOkaGrauert.TransportOperator

open TrivSqZeroExt

variable {R : Type*} [Ring R] (D : TransportOperator R)

/-- Extend transport coefficientwise to the ring with `ε² = 0`. -/
def onDual : TransportOperator (DualNumber R) where
  X := {
    toFun := fun q => (D.X q.fst, D.X q.snd)
    map_zero' := by ext <;> simp
    map_add' := by intros; ext <;> simp }
  leibniz q p := by
    apply TrivSqZeroExt.ext
    · simp [D.leibniz]
    · simp [D.leibniz]
      abel

/-- The infinitesimal group element `1 + εH` has inverse `1 - εH`. -/
def infinitesimalUnit (H : R) : (DualNumber R)ˣ where
  val := (1, H)
  inv := (1, -H)
  val_inv := by ext <;> simp
  inv_val := by ext <;> simp

/-- The additive operator `XH + [A,H]` on infinitesimal gauges. -/
def linearizedAt (A : R) : R →+ R where
  toFun H := D.X H + (A * H - H * A)
  map_zero' := by simp
  map_add' H K := by simp [add_mul, mul_add]; abel

/-- Simultaneous variation of the attenuation `A + εB` and the gauge
`1 + εH`. The coefficients can be noncommuting matrices. -/
theorem gauge_firstVariation (A B H : R) :
    D.onDual.gauge (A, B) (infinitesimalUnit H) =
      (A, B + D.linearizedAt A H) := by
  apply TrivSqZeroExt.ext
  · simp [gauge, onDual, infinitesimalUnit]
  · simp [gauge, onDual, infinitesimalUnit, linearizedAt]
    abel

/-- With the attenuation held fixed, the gauge orbit has first-order term
`XH + AH - HA`. -/
theorem orbit_firstVariation (A H : R) :
    D.onDual.gauge (inl A) (infinitesimalUnit H) =
      (A, D.linearizedAt A H) := by
  simpa [inl] using D.gauge_firstVariation A 0 H

/-- Lift a finite gauge as a constant dual number. -/
def constantUnit (g : Rˣ) : (DualNumber R)ˣ :=
  Units.map (inlHom R R).toMonoidHom g

private theorem gauge_constantUnit (A : R) (g : Rˣ) :
    D.onDual.gauge (inl A) (constantUnit g) = inl (D.gauge A g) := by
  apply TrivSqZeroExt.ext
  · change (g⁻¹ : Rˣ) * (D.X (g : R) + A * (g : R)) = _
    rfl
  · simp [gauge, onDual, constantUnit, Units.map, inlHom]

/-- Along the translated orbit `g(1 + εH)`, the same linearization acts at
the attenuation already transformed by `g`. -/
theorem translated_orbit_firstVariation (A H : R) (g : Rˣ) :
    D.onDual.gauge (inl A) (constantUnit g * infinitesimalUnit H) =
      (D.gauge A g, D.linearizedAt (D.gauge A g) H) := by
  rw [gauge_mul, D.gauge_constantUnit, D.orbit_firstVariation]

end TransportOkaGrauert.TransportOperator
