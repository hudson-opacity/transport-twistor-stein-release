import TransportOkaGrauert.Triangular

/-! User-facing flat disk result in ordinary base coordinates, with independent
complex coefficients for each Laurent polynomial entry of the attenuation. -/
namespace TransportOkaGrauert.PolynomialDisk

open FlatScalar
open scoped ComplexConjugate ContDiff
noncomputable section

/-- On |w|=1 this is c z^p conj(z)^q w^(k−1); the allowed frequencies start at −1. -/
structure Monomial where
  c : ℂ
  p : ℕ
  q : ℕ
  k : ℕ

def Monomial.eval (m : Monomial) (z w : ℂ) :=
  m.c * z ^ m.p * conj z ^ m.q * w ^ m.k * conj w

def eval (P : List Monomial) (z w : ℂ) := (P.map (fun m => m.eval z w)).sum

/-- Multiplication by z = u + w² conj(z) in characteristic coordinates. -/
private def timesZ (t : Term) : List Term :=
  [{ t with p := t.p + 1 }, { t with k := t.k + 2, q := t.q + 1 }]

private theorem timesZ_spec (t : Term) (z w : ℂ) :
    attenuation (timesZ t) z w = z * t.attenuation z w := by
  simp [timesZ, attenuation, Term.attenuation, Term.coeff, pow_succ]
  unfold firstIntegral
  ring

private theorem attenuation_append (a b : List Term) (z w : ℂ) :
    attenuation (a ++ b) z w = attenuation a z w + attenuation b z w := by
  simp [attenuation]

private theorem timesZ_all (a : List Term) (z w : ℂ) :
    attenuation (a.flatMap timesZ) z w = z * attenuation a z w := by
  induction a with
  | nil => simp [attenuation]
  | cons t ts ih =>
    rw [List.flatMap_cons, attenuation_append, timesZ_spec, ih]
    exact (mul_add _ _ _).symm

private def timesZPow (n : ℕ) (a : List Term) : List Term :=
  match n with
  | 0 => a
  | n+1 => (timesZPow n a).flatMap timesZ

private theorem timesZPow_spec (n : ℕ) (a : List Term) (z w : ℂ) :
    attenuation (timesZPow n a) z w = z ^ n * attenuation a z w := by
  induction n with
  | zero => simp [timesZPow]
  | succ n ih => rw [timesZPow, timesZ_all, ih, pow_succ]; ring

def expand (P : List Monomial) : List Term :=
  P.flatMap (fun m => timesZPow m.p [⟨m.c, 0, m.k, m.q⟩])

theorem expand_spec (P : List Monomial) (z w : ℂ) :
    attenuation (expand P) z w = eval P z w := by
  induction P with
  | nil => simp [expand, attenuation, eval]
  | cons m ms ih =>
    change attenuation (timesZPow m.p [_] ++ expand ms) _ _ = m.eval z w + eval ms z w
    rw [attenuation_append, timesZPow_spec, ih]
    simp [Monomial.eval, attenuation, Term.attenuation, Term.coeff]
    ring

/-- Holomorphic scalar integrating factors for every finite polynomial attenuation
in z, conj(z), and angular powers ≥ −1 on the flat disk (in fact, on the plane). -/
theorem scalar (P : List Monomial) :
    ∃ F G : ℂ → ℂ → ℂ,
      ContDiff ℝ ∞ (fun p : ℂ × ℂ => F p.1 p.2) ∧ ContDiff ℝ ∞ (fun p : ℂ × ℂ => G p.1 p.2) ∧
      (∀ z, Differentiable ℂ (F z) ∧ Differentiable ℂ (G z)) ∧
      (∀ z w, F z w * G z w = 1) ∧
      ∀ z w, w * conj w = 1 →
        HasDerivAt (fun t : ℝ => F (z + t * w) w) (-(eval P z w * F z w)) 0 := by
  let a := expand P
  have h := flatScalarIntegratingFactor a
  exact ⟨factor a, inverseFactor a, (factor_smooth a).1, (factor_smooth a).2,
    fun z => ⟨(h z).1, (h z).2.1⟩, fun z => (h z).2.2.1,
    fun z w hw => by simpa [a, expand_spec] using (h z).2.2.2 w hw⟩

open scoped Matrix

def upper (P Q S : List Monomial) (z w : ℂ) : Mat₃ :=
  !![0, eval P z w, eval S z w; 0, 0, eval Q z w; 0, 0, 0]

/-- A noncommutative class: all strictly upper triangular 3×3 attenuations with
polynomial base coefficients and a finite fibre Laurent series of order at least −1. -/
theorem triangular (P Q S : List Monomial) :
    ∃ F G : ℂ → ℂ → Mat₃,
      (∀ i j, ContDiff ℝ ∞ (fun p : ℂ × ℂ => F p.1 p.2 i j) ∧
        ContDiff ℝ ∞ (fun p : ℂ × ℂ => G p.1 p.2 i j)) ∧
      (∀ z i j, Differentiable ℂ (fun w => F z w i j) ∧
        Differentiable ℂ (fun w => G z w i j)) ∧
      (∀ z w, F z w * G z w = 1 ∧ G z w * F z w = 1) ∧
      ∀ z w, w * conj w = 1 → ∀ i j,
        HasDerivAt (fun t : ℝ => F (z + t * w) w i j)
          (-(upper P Q S z w * F z w) i j) 0 := by
  let a := expand P
  let b := expand Q
  let c := expand S
  exact ⟨triangularF a b c, triangularInverse a b c, triangular_smooth a b c,
    triangular_entire a b c, triangular_inverses a b c,
    fun z w hw i j => by simpa [upper, triangularA, a, b, c, expand_spec] using
      triangular_transport a b c z w hw i j⟩

end
end TransportOkaGrauert.PolynomialDisk
