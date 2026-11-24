import TransportOkaGrauert.JumpingLines
import TransportOkaGrauert.BirkhoffCell
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# Prescribing finitely many exceptional Birkhoff fibres

Apply a complex polynomial to the Euclidean first integral. At each base point,
a single right shear, polynomial in the velocity and invertible on the whole
velocity plane, reduces the new loop to the standard loop with constant
off-diagonal entry `p.eval z`. Its construction uses polynomial division and
extends over roots of `p` as well as over zero velocity.
-/

noncomputable section
namespace TransportOkaGrauert.PolynomialJumps

open Polynomial
open scoped Polynomial ComplexConjugate Matrix ContDiff

/-- A determinant-one loop on every velocity circle. -/
def W (p : Polynomial ℂ) (z w : ℂ) : JumpingLines.Mat :=
  !![w, p.eval (FlatScalar.firstIntegral z w); 0, w⁻¹]

theorem W_det (p : Polynomial ℂ) (z : ℂ) {w : ℂ} (hw : w ≠ 0) :
    (W p z w).det = 1 := by
  simp [W, Matrix.det_fin_two, hw]

theorem W_advance (p : Polynomial ℂ) (z : ℂ) (v : Circle) (t : ℝ) :
    W p (z + t * v) v = W p z v := by
  have hu : (v : ℂ) * conj (v : ℂ) = 1 := by
    rw [← Circle.coe_inv_eq_conj, Circle.coe_inv, mul_inv_cancel₀ v.coe_ne_zero]
  simp only [W, FlatScalar.firstIntegral_advance _ _ hu]

theorem W_smooth (p : Polynomial ℂ) (i j : Fin 2) :
    ContDiff ℝ ∞ (fun x : ℂ × ℝ => W p x.1 (Circle.exp x.2) i j) := by
  have hp : ContDiff ℂ ∞ (fun u => p.eval u) := by
    simpa only [Polynomial.aeval_def, Polynomial.eval₂_id] using (p.contDiff_aeval (𝕜 := ℂ) ∞)
  fin_cases i <;> fin_cases j
  · exact JumpingLines.W_smooth 0 0
  · exact (hp.restrict_scalars ℝ).comp (JumpingLines.W_smooth 0 1)
  · exact contDiff_const
  · exact JumpingLines.W_smooth 1 1

theorem W_transport (p : Polynomial ℂ) (z : ℂ) (v : Circle) (i j : Fin 2) :
    Fourier.flatX (fun x w => W p x w i j) z v = 0 := by
  have hangle := (W_smooth p i j).comp
    (contDiff_id.prodMk (contDiff_const (c := Complex.arg (v : ℂ))))
  have hb : DifferentiableAt ℝ (fun x => W p x v i j) z := by
    simpa only [Function.comp_def, id_eq, Circle.exp_arg] using
      (hangle.differentiable (by decide)).differentiableAt (x := z)
  have hd := TwistorDisk.line_derivative (fun x w => W p x w i j) z v hb
  simp only [W_advance] at hd
  exact hd.unique (hasDerivAt_const 0 _)

/-- This polynomial quotient satisfies the divided-difference identity even
when the two evaluation points coincide. -/
def quotient (p : Polynomial ℂ) (z : ℂ) : Polynomial ℂ := p /ₘ (X - C z)

theorem divided_difference (p : Polynomial ℂ) (z u : ℂ) :
    p.eval z + (u - z) * (quotient p z).eval u = p.eval u := by
  have h := congrArg (fun q : Polynomial ℂ => q.eval u)
    (Polynomial.modByMonic_add_div p (Polynomial.monic_X_sub_C z))
  simpa [quotient] using h

/-- Multiplication by `w` recovers the difference between the two off-diagonal
entries, without any division by the velocity. -/
def shearEntry (p : Polynomial ℂ) (z w : ℂ) : ℂ :=
  -(w * conj z) * (quotient p z).eval (FlatScalar.firstIntegral z w)

theorem shearEntry_spec (p : Polynomial ℂ) (z w : ℂ) :
    p.eval z + w * shearEntry p z w = p.eval (FlatScalar.firstIntegral z w) := by
  rw [← divided_difference p z (FlatScalar.firstIntegral z w)]
  unfold shearEntry FlatScalar.firstIntegral
  ring

def shear (p : Polynomial ℂ) (z w : ℂ) : JumpingLines.Mat :=
  !![1, shearEntry p z w; 0, 1]

def shearInv (p : Polynomial ℂ) (z w : ℂ) : JumpingLines.Mat :=
  !![1, -shearEntry p z w; 0, 1]

theorem shear_inverses (p : Polynomial ℂ) (z w : ℂ) :
    shear p z w * shearInv p z w = 1 ∧ shearInv p z w * shear p z w = 1 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [shear, shearInv, Matrix.mul_apply, Fin.sum_univ_two]

theorem shear_entire (p : Polynomial ℂ) (z : ℂ) (i j : Fin 2) :
    Differentiable ℂ (fun w => shear p z w i j) ∧
    Differentiable ℂ (fun w => shearInv p z w i j) := by
  have hu : Differentiable ℂ (FlatScalar.firstIntegral z) := by
    unfold FlatScalar.firstIntegral
    fun_prop
  have he : Differentiable ℂ (shearEntry p z) :=
    ((differentiable_id.mul_const (conj z)).neg).mul ((quotient p z).differentiable.comp hu)
  constructor <;> fin_cases i <;> fin_cases j <;>
    first | exact he | exact he.neg | exact differentiable_const _

/-- The two loops differ on the right by an everywhere-invertible holomorphic
factor. The identity holds at every base point, including all roots of `p`. -/
theorem reduction (p : Polynomial ℂ) (z w : ℂ) :
    W p z w = (!![w, p.eval z; 0, w⁻¹] : JumpingLines.Mat) * shear p z w := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [W, shear, Matrix.mul_apply, Fin.sum_univ_two]
  simpa [add_comm] using (shearEntry_spec p z w).symm

/-- A polynomial whose set of complex roots is the prescribed finite set. -/
def rootPolynomial (S : Finset ℂ) : Polynomial ℂ := ∏ a ∈ S, (X - C a)

theorem rootPolynomial_eval_eq_zero_iff (S : Finset ℂ) (z : ℂ) :
    (rootPolynomial S).eval z = 0 ↔ z ∈ S := by
  simp [rootPolynomial, Polynomial.eval_prod, Finset.prod_eq_zero_iff, sub_eq_zero]

/-- Canonical factorization occurs precisely away from the roots of the
polynomial. This includes the identically zero and constant polynomial cases. -/
theorem bigCell_iff (p : Polynomial ℂ) (z : ℂ) :
    BirkhoffCell.BigCell (fun v => W p z v) ↔ p.eval z ≠ 0 := by
  let S := BirkhoffCell.Factor.ofEntire (shear p z) (shearInv p z)
    (shear_entire p z) (shear_inverses p z)
  have he : (fun v : Circle => W p z v) =
      fun v : Circle => BirkhoffCell.standard (p.eval z) v * S.val v :=
    funext (fun v => reduction p z v)
  rw [he, BirkhoffCell.bigCell_right_iff (fun v => BirkhoffCell.standard (p.eval z) v) S,
    BirkhoffCell.standard_big_iff]

/-- The exceptional fibres are exactly the members of the prescribed set. -/
theorem prescribed_jumps (S : Finset ℂ) (z : ℂ) :
    BirkhoffCell.BigCell (fun v => W (rootPolynomial S) z v) ↔ z ∉ S :=
  (bigCell_iff _ _).trans (not_congr (rootPolynomial_eval_eq_zero_iff S z))

end TransportOkaGrauert.PolynomialJumps
