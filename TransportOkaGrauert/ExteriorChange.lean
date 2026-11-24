import TransportOkaGrauert.BirkhoffCell

/-! Changing the exterior factor in the canonical Birkhoff cell. -/

noncomputable section
namespace TransportOkaGrauert.BirkhoffCell

open Metric
open scoped Matrix

/-- Freeze a disk factor and its inverse at the chart origin. In the
exterior chart this point is infinity. -/
def Factor.center (X : Factor) : Factor where
  val _ := X.val 0
  inv _ := X.inv 0
  regular _ _ := differentiable_const _ |>.diffContOnCl
  regularInv _ _ := differentiable_const _ |>.diffContOnCl
  inverses _ _ := X.inverses 0 (by simp)

/-- Right multiplication by the inverse constant makes the exterior
factor equal to the identity at infinity. -/
def Factor.normalizeExterior (X : Factor) : Factor := X.times X.center.swap

@[simp] theorem Factor.normalizeExterior_zero (X : Factor) :
    X.normalizeExterior.val 0 = 1 := (X.inverses 0 (by simp)).1

/-- A factorization with an arbitrary invertible exterior value at infinity
can be normalized by transferring that constant to the inside factor. -/
theorem bigCell_of_unnormalized (L : Loop) (X F : Factor)
    (h : ∀ v : Circle, L v = X.val (v : ℂ)⁻¹ * F.val v) : BigCell L := by
  refine ⟨X.normalizeExterior, X.center.times F, X.normalizeExterior_zero, ?_⟩
  intro v
  change L v = (X.val (v : ℂ)⁻¹ * X.inv 0) * (X.val 0 * F.val v)
  rw [h, mul_assoc, ← mul_assoc (X.inv 0), (X.inverses 0 (by simp)).2, one_mul]

private theorem bigCell_left (L : Loop) (S : Factor) (hL : BigCell L) :
    BigCell (fun v => S.val (v : ℂ)⁻¹ * L v) := by
  obtain ⟨G, F, _, h⟩ := hL
  apply bigCell_of_unnormalized _ (S.times G) F
  intro v
  change S.val (v : ℂ)⁻¹ * L v = (S.val (v : ℂ)⁻¹ * G.val (v : ℂ)⁻¹) * F.val v
  rw [h, mul_assoc]

/-- An invertible exterior factor preserves membership in the canonical
cell, including when its value at infinity is not the identity. -/
theorem bigCell_left_iff (L : Loop) (S : Factor) :
    BigCell (fun v => S.val (v : ℂ)⁻¹ * L v) ↔ BigCell L := by
  refine ⟨fun h => ?_, bigCell_left L S⟩
  have h' := bigCell_left _ S.swap h
  have hcancel (v : Circle) : S.inv (v : ℂ)⁻¹ * S.val (v : ℂ)⁻¹ = 1 := by
    apply (S.inverses _ _).2
    simp [Metric.mem_closedBall]
  simpa only [Factor.swap, ← mul_assoc, hcancel, one_mul] using h'

/-- Upper elementary shear, with inverse obtained by negating its entry. -/
def upperShear (a : ℂ) : Mat := !![1, a; 0, 1]

@[simp] theorem upperShear_det (a : ℂ) : (upperShear a).det = 1 := by
  simp [upperShear, Matrix.det_fin_two]

private theorem regular_upperShear {a : ℂ → ℂ} (ha : DiffContOnCl ℂ a (ball 0 1))
    (i j : Fin 2) : DiffContOnCl ℂ (fun w => upperShear (a w) i j) (ball 0 1) := by
  fin_cases i <;> fin_cases j <;> simp [upperShear]
  all_goals first | exact ha | exact (differentiable_const _).diffContOnCl

/-- Fill an upper shear by a prescribed scalar function in either disk chart. -/
def upperFactor (a : ℂ → ℂ) (ha : DiffContOnCl ℂ a (ball 0 1)) : Factor where
  val w := upperShear (a w)
  inv w := upperShear (-(a w))
  regular := regular_upperShear ha
  regularInv := regular_upperShear ⟨ha.differentiableOn.neg, ha.continuousOn.neg⟩
  inverses w _ := by
    constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [upperShear, Matrix.mul_apply, Fin.sum_univ_two]

end TransportOkaGrauert.BirkhoffCell
