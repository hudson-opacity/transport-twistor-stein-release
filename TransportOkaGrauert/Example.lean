import Std

/-!
# A polynomial integrating factor for straight-line transport

On the Euclidean plane, write the base point as `z` and a unit tangent vector
as `w`. Along the geodesic `z + t w`, the scalar `conj(z) w` increases by
exactly `t`. For the constant matrix attenuation `N = E₁₂`, this gives the
integrating factor `F = I - conj(z) w N` and inverse `I + conj(z) w N`.
Both are polynomials of degree at most one in the fiber variable.

The calculation uses pairs of coordinates over any commutative ring. It
proves the exact finite transport identity, which implies the usual
differential equation over the real numbers. No limiting operation, Fourier
integral, or choice of function space is required for this polynomial case.
-/

namespace TransportOkaGrauert.FlatExample

/-- Real and imaginary coordinates, with the standard complex multiplication. -/
@[ext] structure Coord (R : Type) where
  re : R
  im : R

variable {R : Type} [Lean.Grind.CommRing R]

namespace Coord

def zero : Coord R := ⟨0, 0⟩
def one : Coord R := ⟨1, 0⟩
def add (z w : Coord R) : Coord R := ⟨z.re + w.re, z.im + w.im⟩
def neg (z : Coord R) : Coord R := ⟨-z.re, -z.im⟩
def mul (z w : Coord R) : Coord R :=
  ⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩
def conj (z : Coord R) : Coord R := ⟨z.re, -z.im⟩
def scale (t : R) (z : Coord R) : Coord R := ⟨t * z.re, t * z.im⟩

end Coord

/-- The unit-circle relation on the fiber coordinate. -/
def UnitDirection (w : Coord R) : Prop := w.re * w.re + w.im * w.im = 1

/-- The straight geodesic with initial position `z` and velocity `w`. -/
def advance (z w : Coord R) (t : R) : Coord R := z.add (w.scale t)

def primitive (z w : Coord R) : Coord R := z.conj.mul w

theorem primitive_advance (z w : Coord R) (hw : UnitDirection w) (t : R) :
    primitive (advance z w t) w = (primitive z w).add ⟨t, 0⟩ := by
  unfold UnitDirection at hw
  ext <;> simp only [primitive, advance, Coord.add, Coord.mul, Coord.conj, Coord.scale] <;> grind

@[ext] structure Matrix₂ (R : Type) where
  a : Coord R
  b : Coord R
  c : Coord R
  d : Coord R

namespace Matrix₂

def id : Matrix₂ R := ⟨.one, .zero, .zero, .one⟩
def add (u v : Matrix₂ R) : Matrix₂ R :=
  ⟨u.a.add v.a, u.b.add v.b, u.c.add v.c, u.d.add v.d⟩
def scale (k : Coord R) (u : Matrix₂ R) : Matrix₂ R :=
  ⟨k.mul u.a, k.mul u.b, k.mul u.c, k.mul u.d⟩
def mul (u v : Matrix₂ R) : Matrix₂ R :=
  ⟨(u.a.mul v.a).add (u.b.mul v.c), (u.a.mul v.b).add (u.b.mul v.d),
   (u.c.mul v.a).add (u.d.mul v.c), (u.c.mul v.b).add (u.d.mul v.d)⟩

end Matrix₂

/-- Matrix whose sole possibly nonzero entry is in position (1, 2). -/
def upper (u : Coord R) : Matrix₂ R := ⟨.zero, u, .zero, .zero⟩

def attenuation : Matrix₂ R := upper .one

def shear (u : Coord R) : Matrix₂ R := ⟨.one, u, .zero, .one⟩

def factor (z w : Coord R) : Matrix₂ R := shear (primitive z w).neg
def inverseFactor (z w : Coord R) : Matrix₂ R := shear (primitive z w)

/-- Explicit polynomial certificate using only the constant and first fiber powers. -/
def FiberAffine (f : Coord R → Coord R → Matrix₂ R) : Prop :=
  ∀ z, ∃ c₀ c₁ : Matrix₂ R, ∀ w, f z w = c₀.add (c₁.scale w)

private theorem shear_mul (u v : Coord R) :
    (shear u).mul (shear v) = shear (u.add v) := by
  ext <;> simp only [shear, Matrix₂.mul, Coord.mul, Coord.add, Coord.zero, Coord.one] <;> grind

theorem factor_inverses (z w : Coord R) :
    (factor z w).mul (inverseFactor z w) = Matrix₂.id ∧
    (inverseFactor z w).mul (factor z w) = Matrix₂.id := by
  simp only [factor, inverseFactor, shear_mul]
  constructor <;> ext <;> simp only [shear, Matrix₂.id, Coord.add, Coord.neg, Coord.zero] <;> grind

theorem factors_fiber_affine : FiberAffine (factor (R := R)) ∧ FiberAffine (inverseFactor (R := R)) := by
  constructor
  · intro z
    refine ⟨Matrix₂.id, upper z.conj.neg, ?_⟩
    intro w
    ext <;> simp only [factor, shear, primitive, upper, Matrix₂.id, Matrix₂.add,
      Matrix₂.scale, Coord.add, Coord.mul, Coord.neg, Coord.conj, Coord.zero] <;> grind
  · intro z
    refine ⟨Matrix₂.id, upper z.conj, ?_⟩
    intro w
    ext <;> simp only [inverseFactor, shear, primitive, upper, Matrix₂.id, Matrix₂.add,
      Matrix₂.scale, Coord.add, Coord.mul, Coord.conj, Coord.zero] <;> grind

/-- Along every straight unit-speed geodesic, the increment in `F` is exactly
`-t N F`. Differentiating this affine identity at zero gives `XF + NF = 0`. -/
theorem factor_transport (z w : Coord R) (hw : UnitDirection w) (t : R) :
    (factor (advance z w t) w).add (((attenuation (R := R)).mul (factor z w)).scale ⟨t, 0⟩)
      = factor z w := by
  simp only [factor, primitive_advance z w hw t]
  ext <;> simp only [attenuation, shear, upper, Matrix₂.add, Matrix₂.scale, Matrix₂.mul,
    Coord.add, Coord.mul, Coord.neg, Coord.zero, Coord.one] <;> grind

end TransportOkaGrauert.FlatExample
