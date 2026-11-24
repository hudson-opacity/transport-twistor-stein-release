import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# A finite polynomial inverse for unipotent upper triangular matrices

A nonzero entry in a product of `k` strictly upper triangular matrices
must advance at least `k` places to the right. For an `n × n` matrix the
`n`th power therefore vanishes, and the geometric sum of lower powers of
`-N` inverts `1 + N` over any ring.
-/

namespace TransportOkaGrauert.Nilpotent

open Finset
open scoped ContDiff

variable {n : ℕ} {R : Type*}

/-- Strict upper triangularity, including the zero diagonal. -/
def StrictUpper [Zero R] (N : Matrix (Fin n) (Fin n) R) : Prop :=
  ∀ i j, j ≤ i → N i j = 0

/-- A power has zeros on every diagonal strictly below its power index.
Unlike a determinant argument this works over a noncommutative semiring. -/
theorem power_entry_zero [Semiring R] {N : Matrix (Fin n) (Fin n) R}
    (hN : StrictUpper N) (k : ℕ) (i j : Fin n) (hij : j.val < i.val + k) :
    (N ^ k) i j = 0 := by
  induction k generalizing i j with
  | zero =>
    have h : i ≠ j := by intro he; subst j; omega
    simp [h]
  | succ k ih =>
    rw [pow_succ, Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro b _
    by_cases hb : b.val < i.val + k
    · rw [ih i b hb, zero_mul]
    · have hjb : j ≤ b := by change j.val ≤ b.val; omega
      rw [hN b j hjb, mul_zero]

/-- A strictly upper triangular matrix of size `n` is killed by the `n`th power. -/
theorem pow_dimension_eq_zero [Semiring R] {N : Matrix (Fin n) (Fin n) R}
    (hN : StrictUpper N) : N ^ n = 0 := by
  ext i j
  exact power_entry_zero hN n i j (by have := j.isLt; omega)

/-- The inverse is a polynomial with integer coefficients in the matrix entries. -/
def finiteInverse [Ring R] (N : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R :=
  ∑ k ∈ range n, (-N) ^ k

theorem finiteInverse_apply [Ring R] (N : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    finiteInverse N i j = ∑ k ∈ range n, ((-N) ^ k) i j := by
  simp [finiteInverse, Matrix.sum_apply]

/-- The finite geometric sum inverts `1 + N` on both sides. -/
theorem finiteInverse_spec [Ring R] {N : Matrix (Fin n) (Fin n) R} (hN : StrictUpper N) :
    (1 + N) * finiteInverse N = 1 ∧ finiteInverse N * (1 + N) = 1 := by
  have hn : StrictUpper (-N) := fun i j h => by simp [hN i j h]
  have hp := pow_dimension_eq_zero hn
  exact ⟨by simpa [finiteInverse, hp] using mul_neg_geom_sum (-N) n,
    by simpa [finiteInverse, hp] using geom_sum_mul_neg (-N) n⟩

/-- The polynomial inverse commutes with evaluation of its coefficients. -/
theorem finiteInverse_map {S : Type*} [Ring R] [Ring S] (φ : R →+* S)
    (N : Matrix (Fin n) (Fin n) R) :
    φ.mapMatrix (finiteInverse N) = finiteInverse (φ.mapMatrix N) := by
  simp only [finiteInverse, map_sum, map_pow, map_neg]

/-- If the input entries belong to a ring of functions, so do the inverse
entries. This gives the same formula for polynomial, smooth, or holomorphic
coefficients. -/
theorem finiteInverse_entry_mem {X : Type*} [Ring R] (S : Subring (X → R))
    (N : X → Matrix (Fin n) (Fin n) R) (hN : ∀ i j, (fun x => N x i j) ∈ S) (i j : Fin n) :
    (fun x => finiteInverse (N x) i j) ∈ S := by
  let A : Matrix (Fin n) (Fin n) S := fun a b => ⟨_, hN a b⟩
  have h : (finiteInverse A i j).val = (fun x => finiteInverse (N x) i j) := by
    funext x
    let ev := (Pi.evalRingHom (fun _ : X => R) x).comp S.subtype
    exact congrArg (fun M : Matrix (Fin n) (Fin n) R => M i j) (finiteInverse_map ev A)
  rw [← h]
  exact (finiteInverse A i j).property

/-- Holomorphic dependence in the fiber survives entrywise inversion. -/
theorem finiteInverse_differentiable (N : ℂ → Matrix (Fin n) (Fin n) ℂ)
    (hN : ∀ i j, Differentiable ℂ (fun w => N w i j)) (i j : Fin n) :
    Differentiable ℂ (fun w => finiteInverse (N w) i j) := by
  let S : Subring (ℂ → ℂ) := {
    carrier := {f | Differentiable ℂ f}
    zero_mem' := differentiable_const _
    one_mem' := differentiable_const _
    add_mem' := by intro f g hf hg; simp only [Set.mem_setOf_eq] at *; exact Differentiable.add hf hg
    neg_mem' := by intro f hf; simp only [Set.mem_setOf_eq] at *; exact Differentiable.neg hf
    mul_mem' := by intro f g hf hg; simp only [Set.mem_setOf_eq] at *; exact Differentiable.mul hf hg }
  exact finiteInverse_entry_mem S N hN i j

/-- Smooth dependence on base point and direction survives entrywise inversion. -/
theorem finiteInverse_smooth (N : ℂ × ℂ → Matrix (Fin n) (Fin n) ℂ)
    (hN : ∀ i j, ContDiff ℝ ∞ (fun p => N p i j)) (i j : Fin n) :
    ContDiff ℝ ∞ (fun p => finiteInverse (N p) i j) := by
  let S : Subring ((ℂ × ℂ) → ℂ) := {
    carrier := {f | ContDiff ℝ ∞ f}
    zero_mem' := by simp only [Set.mem_setOf_eq]; exact contDiff_const (c := (0 : ℂ))
    one_mem' := by simp only [Set.mem_setOf_eq]; exact contDiff_const (c := (1 : ℂ))
    add_mem' := by intro f g hf hg; simp only [Set.mem_setOf_eq] at *; exact ContDiff.add hf hg
    neg_mem' := by intro f hf; simp only [Set.mem_setOf_eq] at *; exact ContDiff.neg hf
    mul_mem' := by intro f g hf hg; simp only [Set.mem_setOf_eq] at *; exact ContDiff.mul hf hg }
  exact finiteInverse_entry_mem S N hN i j

end TransportOkaGrauert.Nilpotent
