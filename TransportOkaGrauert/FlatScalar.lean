import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Tactic

/-! A direct scalar transport calculation along straight unit-speed geodesics.
The conserved coordinate z - w² conj(z) allows base-dependent coefficients.
The construction extends both the factor and its inverse to the entire velocity plane. -/
namespace TransportOkaGrauert.FlatScalar

noncomputable section
open scoped ComplexConjugate ContDiff

/-- Polynomial coordinates adapted to the straight geodesic field. -/
def firstIntegral (z w : ℂ) := z - w ^ 2 * conj z

theorem firstIntegral_advance (z w : ℂ) (hw : w * conj w = 1) (t : ℝ) :
    firstIntegral (z + t * w) w = firstIntegral z w := by
  have hv : w ^ 2 * conj w = w := by rw [pow_two, mul_assoc, hw, mul_one]
  simp only [firstIntegral, map_add, map_mul, Complex.conj_ofReal]
  linear_combination -(t : ℂ) * hv

/-- A term c u^p w^k s^q in the coordinates u=z−w²s and s=conj(z).
On the unit circle the attenuation also has an overall factor w⁻¹. -/
structure Term where
  c : ℂ
  p : ℕ
  k : ℕ
  q : ℕ

def Term.coeff (m : Term) (z w : ℂ) := m.c * firstIntegral z w ^ m.p * w ^ m.k

def Term.attenuation (m : Term) (z w : ℂ) := m.coeff z w * conj z ^ m.q * conj w

def Term.primitive (m : Term) (z w : ℂ) :=
  m.coeff z w / (m.q + 1 : ℂ) * conj z ^ (m.q + 1)

theorem Term.transport (m : Term) (z w : ℂ) (hw : w * conj w = 1) :
    HasDerivAt (fun t : ℝ => m.primitive (z + t * w) w) (m.attenuation z w) 0 := by
  have hd : HasDerivAt (fun t : ℂ => conj z + t * conj w) (conj w) 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).mul_const (conj w)).const_add (conj z)
  have hp := ((hd.pow (m.q + 1)).const_mul (m.coeff z w / (m.q + 1 : ℂ))).comp_ofReal
  simp only [zero_mul, add_zero, Nat.add_sub_cancel,
    Nat.cast_add, Nat.cast_one] at hp
  convert hp using 1
  · ext t
    simp [Term.primitive, Term.coeff, firstIntegral_advance z w hw]
  · unfold Term.attenuation
    have hn : (m.q : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m.q
    field_simp

def primitive (terms : List Term) (z w : ℂ) := (terms.map (fun m => m.primitive z w)).sum
def attenuation (terms : List Term) (z w : ℂ) := (terms.map (fun m => m.attenuation z w)).sum

theorem transport (terms : List Term) (z w : ℂ) (hw : w * conj w = 1) :
    HasDerivAt (fun t : ℝ => primitive terms (z + t * w) w) (attenuation terms z w) 0 := by
  induction terms with
  | nil => simpa [primitive, attenuation] using (hasDerivAt_const (0 : ℝ) (0 : ℂ))
  | cons m l ih => simpa [primitive, attenuation] using (m.transport z w hw).add ih

theorem primitive_entire (terms : List Term) (z : ℂ) : Differentiable ℂ (primitive terms z) := by
  induction terms with
  | nil => exact differentiable_const _
  | cons m l ih =>
    change Differentiable ℂ (fun w => m.primitive z w + primitive l z w)
    unfold Term.primitive Term.coeff firstIntegral
    fun_prop

def factor (terms : List Term) (z w : ℂ) := Complex.exp (-primitive terms z w)
def inverseFactor (terms : List Term) (z w : ℂ) := Complex.exp (primitive terms z w)

/-- Smooth up to the boundary of any closed base and fibre disks, by extension
to an ambient polynomial on the product of two planes. -/
theorem primitive_smooth (terms : List Term) :
    ContDiff ℝ ∞ (fun p : ℂ × ℂ => primitive terms p.1 p.2) := by
  induction terms with
  | nil => exact contDiff_const
  | cons m l ih =>
    change ContDiff ℝ ∞ (fun p : ℂ × ℂ => m.primitive p.1 p.2 + primitive l p.1 p.2)
    apply ContDiff.add _ ih
    unfold Term.primitive Term.coeff firstIntegral
    have hc : ContDiff ℝ ∞ (fun p : ℂ × ℂ => conj p.1) :=
      Complex.conjCLE.contDiff.comp contDiff_fst
    fun_prop

theorem factor_smooth (terms : List Term) :
    ContDiff ℝ ∞ (fun p : ℂ × ℂ => factor terms p.1 p.2) ∧
    ContDiff ℝ ∞ (fun p : ℂ × ℂ => inverseFactor terms p.1 p.2) :=
  ⟨(primitive_smooth terms).neg.cexp, (primitive_smooth terms).cexp⟩

/-- Explicit holomorphic integrating factor for a family of position-dependent scalar
attenuations. The last conjunct is the geodesic transport equation XF = −AF. -/
theorem flatScalarIntegratingFactor (terms : List Term) (z : ℂ) :
    Differentiable ℂ (factor terms z) ∧ Differentiable ℂ (inverseFactor terms z) ∧
    (∀ w, factor terms z w * inverseFactor terms z w = 1) ∧
    ∀ w, w * conj w = 1 →
      HasDerivAt (fun t : ℝ => factor terms (z + t * w) w)
        (-(attenuation terms z w * factor terms z w)) 0 := by
  refine ⟨(primitive_entire terms z).neg.cexp, (primitive_entire terms z).cexp, ?_, ?_⟩
  · intro w
    simp [factor, inverseFactor, ← Complex.exp_add]
  · intro w hw
    simpa [factor, mul_comm] using ((transport terms z w hw).neg.cexp)

end
end TransportOkaGrauert.FlatScalar
