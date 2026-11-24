import TransportOkaGrauert.FlatScalar
import Mathlib.LinearAlgebra.Matrix.Notation

/-! Strictly upper triangular, position-dependent 3×3 attenuations.
The (1,3) entry requires one ordered, iterated primitive. -/
namespace TransportOkaGrauert.FlatScalar
noncomputable section
open scoped ComplexConjugate Matrix ContDiff

private def orderedTerm (a b : Term) : Term where
  c := a.c * (b.c / (b.q + 1 : ℂ))
  p := a.p + b.p
  k := a.k + b.k
  q := a.q + (b.q + 1)

private theorem orderedTerm_attenuation (a b : Term) (z w : ℂ) :
    (orderedTerm a b).attenuation z w = a.attenuation z w * b.primitive z w := by
  simp only [Term.attenuation, Term.primitive, Term.coeff, orderedTerm, pow_add, div_eq_mul_inv]
  ring

def orderedTerms (a b : List Term) := a.flatMap (fun x => b.map (orderedTerm x))

theorem orderedTerms_attenuation (a b : List Term) (z w : ℂ) :
    attenuation (orderedTerms a b) z w = attenuation a z w * primitive b z w := by
  have row (x : Term) : attenuation (b.map (orderedTerm x)) z w =
      x.attenuation z w * primitive b z w := by
    induction b with
    | nil => simp [attenuation, primitive]
    | cons y ys ih =>
      change (orderedTerm x y).attenuation z w + _ = _ * (y.primitive z w + _)
      rw [mul_add, orderedTerm_attenuation]
      exact congrArg (_ + ·) ih
  induction a with
  | nil => simp [orderedTerms, attenuation]
  | cons x xs ih =>
    change attenuation (b.map (orderedTerm x) ++ orderedTerms xs b) z w =
      (x.attenuation z w + attenuation xs z w) * primitive b z w
    simpa [attenuation, add_mul] using congrArg₂ (· + ·) (row x) ih

abbrev Mat₃ := Matrix (Fin 3) (Fin 3) ℂ

private def unipotent (x y z : ℂ) : Mat₃ := !![1, x, z; 0, 1, y; 0, 0, 1]

private theorem unipotent_inverse (x y z : ℂ) :
    unipotent x y z * unipotent (-x) (-y) (x*y-z) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [unipotent, Matrix.mul_apply, Fin.sum_univ_three]
  ring

/-- The listed terms give the independent entries A₁₂, A₂₃ and A₁₃, in that order. -/
def triangularA (a b c : List Term) (z w : ℂ) : Mat₃ :=
  !![0, attenuation a z w, attenuation c z w; 0, 0, attenuation b z w; 0, 0, 0]

def triangularF (a b c : List Term) (z w : ℂ) : Mat₃ :=
  unipotent (-primitive a z w) (-primitive b z w)
    (primitive (orderedTerms a b) z w - primitive c z w)

def triangularInverse (a b c : List Term) (z w : ℂ) : Mat₃ :=
  unipotent (primitive a z w) (primitive b z w)
    (primitive a z w * primitive b z w - (primitive (orderedTerms a b) z w - primitive c z w))

theorem triangular_inverses (a b c : List Term) (z w : ℂ) :
    triangularF a b c z w * triangularInverse a b c z w = 1 ∧
    triangularInverse a b c z w * triangularF a b c z w = 1 := by
  constructor
  · simpa [triangularF, triangularInverse] using unipotent_inverse (-primitive a z w)
      (-primitive b z w) (primitive (orderedTerms a b) z w - primitive c z w)
  · simpa [triangularF, triangularInverse] using unipotent_inverse (primitive a z w)
      (primitive b z w) (primitive a z w * primitive b z w -
        (primitive (orderedTerms a b) z w - primitive c z w))

theorem triangular_entire (a b c : List Term) (z : ℂ) (i j : Fin 3) :
    Differentiable ℂ (fun w => triangularF a b c z w i j) ∧
    Differentiable ℂ (fun w => triangularInverse a b c z w i j) := by
  have ha := primitive_entire a z
  have hb := primitive_entire b z
  have hc := primitive_entire c z
  have hab := primitive_entire (orderedTerms a b) z
  constructor <;> fin_cases i <;> fin_cases j <;>
    simp [triangularF, triangularInverse, unipotent] <;>
    first | apply primitive_entire | fun_prop (disch := apply primitive_entire)

theorem triangular_smooth (a b c : List Term) (i j : Fin 3) :
    ContDiff ℝ ∞ (fun p : ℂ × ℂ => triangularF a b c p.1 p.2 i j) ∧
    ContDiff ℝ ∞ (fun p : ℂ × ℂ => triangularInverse a b c p.1 p.2 i j) := by
  have ha := primitive_smooth a
  have hb := primitive_smooth b
  have hc := primitive_smooth c
  have hab := primitive_smooth (orderedTerms a b)
  constructor <;> fin_cases i <;> fin_cases j <;>
    simp [triangularF, triangularInverse, unipotent] <;> fun_prop

theorem triangular_transport (a b c : List Term) (z w : ℂ) (hw : w * conj w = 1)
    (i j : Fin 3) :
    HasDerivAt (fun t : ℝ => triangularF a b c (z + t * w) w i j)
      (-(triangularA a b c z w * triangularF a b c z w) i j) 0 := by
  have hab := (transport (orderedTerms a b) z w hw).sub (transport c z w hw)
  rw [orderedTerms_attenuation] at hab
  fin_cases i <;> fin_cases j <;>
    simp [triangularF, triangularA, unipotent, Matrix.mul_apply, Fin.sum_univ_three] <;>
    first | exact hasDerivAt_const _ _ | exact (transport a z w hw).neg |
      exact (transport b z w hw).neg | simpa [Pi.sub_def, Pi.add_def, Pi.neg_def, sub_eq_add_neg, add_comm] using hab

end
end TransportOkaGrauert.FlatScalar
