import TransportOkaGrauert.Triangular
import Mathlib.Algebra.BigOperators.Fin

/-!
# Ordered primitives for strictly upper triangular matrix fields

The row recursion terminates because an entry of the attenuation in row
`i` can couple only to rows `k > i`. Products are taken in the order in
which the factors enter the matrix transport equation.
-/

noncomputable section

namespace TransportOkaGrauert.FlatScalar

variable {n : ℕ}

/-- Project an array of polynomial term lists onto its strictly upper part. -/
def upperTerms (a : Fin n → Fin n → List Term) (i j : Fin n) : List Term :=
  if i < j then a i j else []

private def negateTerms (ts : List Term) : List Term :=
  ts.map fun t => {t with c := -t.c}

private theorem attenuation_negateTerms (ts : List Term) (z w : ℂ) :
    attenuation (negateTerms ts) z w = -attenuation ts z w := by
  induction ts with
  | nil => simp [attenuation, negateTerms]
  | cons t ts ih =>
    change ({t with c := -t.c} : Term).attenuation z w + attenuation (negateTerms ts) z w =
      -(t.attenuation z w + attenuation ts z w)
    rw [ih]
    simp [Term.attenuation, Term.coeff, add_comm]

private theorem attenuation_flatten (rows : List (List Term)) (z w : ℂ) :
    attenuation rows.flatten z w = (rows.map (fun row => attenuation row z w)).sum := by
  induction rows with
  | nil => simp [attenuation]
  | cons row rows ih =>
    change attenuation (row ++ rows.flatten) z w = attenuation row z w + _
    simpa only [attenuation, List.map_append, List.sum_append] using
      congrArg (attenuation row z w + ·) ih

/-- List giving the primitive for the `(i,j)` entry, by back substitution. -/
def upperP (a : Fin n → Fin n → List Term) (i j : Fin n) : List Term :=
  if i < j then
    a i j ++ negateTerms ((List.ofFn fun k : Fin n =>
      if _h : i < k then orderedTerms (a i k) (upperP a k j) else []).flatten)
  else []
termination_by n - i.val
decreasing_by exact Nat.sub_lt_sub_left (by omega) _h

theorem upperP_eq_nil (a : Fin n → Fin n → List Term) (i j : Fin n) (h : j ≤ i) :
    upperP a i j = [] := by
  rw [upperP, if_neg (not_lt.mpr h)]

/-- The ordered recurrence is exactly the entry of `A (I - primitive P)`.
It holds at every matrix entry, including those at or below the diagonal. -/
theorem upperP_attenuation (a : Fin n → Fin n → List Term) (i j : Fin n) (z w : ℂ) :
    attenuation (upperP a i j) z w = attenuation (upperTerms a i j) z w -
      ∑ k, attenuation (upperTerms a i k) z w * primitive (upperP a k j) z w := by
  by_cases hij : i < j
  · rw [upperP, if_pos hij]
    have happ (s t : List Term) : attenuation (s ++ t) z w =
        attenuation s z w + attenuation t z w := by simp [attenuation]
    rw [happ, attenuation_negateTerms, attenuation_flatten, List.map_ofFn, Fin.sum_ofFn]
    rw [upperTerms, if_pos hij, sub_eq_add_neg]
    congr 2
    apply Finset.sum_congr rfl
    intro k _
    by_cases hik : i < k
    · simp [Function.comp_apply, hik, upperTerms, orderedTerms_attenuation]
    · simp [Function.comp_apply, hik, upperTerms, attenuation]
  · rw [upperP_eq_nil _ _ _ (le_of_not_gt hij)]
    have hzero (k : Fin n) : attenuation (upperTerms a i k) z w * primitive (upperP a k j) z w = 0 := by
      by_cases hik : i < k
      · have hjk : j ≤ k := (le_of_not_gt hij).trans (le_of_lt hik)
        simp [upperP_eq_nil a k j hjk, primitive]
      · simp [upperTerms, hik, attenuation]
    simp only [hzero, Finset.sum_const_zero, sub_zero]
    simp [upperTerms, hij]

end TransportOkaGrauert.FlatScalar
