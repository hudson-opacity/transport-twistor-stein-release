import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Complex.Circle
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Ring

/-!
# Finite fiber Fourier expansions on the Euclidean plane

Integer powers on the unit circle represent the angular Fourier modes.
Multiplication adds frequency bounds. The actual straight-line geodesic
derivative splits each frequency into its two neighbors.
-/

noncomputable section

namespace TransportOkaGrauert.Fourier

open Complex

/-- The `k`th angular character on the unit circle. -/
def character (k : ℤ) (w : Circle) : ℂ := (w : ℂ) ^ k

theorem character_angle (k : ℤ) (θ : ℝ) :
    character k (Circle.exp θ) = Complex.exp (k * (θ * I)) := by
  rw [Complex.exp_int_mul, character, Circle.coe_exp]

theorem character_add (k l : ℤ) (w : Circle) :
    character (k + l) w = character k w * character l w :=
  zpow_add₀ w.coe_ne_zero _ _

/-- The finite complex linear combinations of characters of frequency at
least `m`, as functions on the unit circle. -/
inductive FiniteModes (m : ℤ) : (Circle → ℂ) → Prop
  | zero : FiniteModes m 0
  | mode (k : ℤ) (hk : m ≤ k) (a : ℂ) :
      FiniteModes m (fun w => a * character k w)
  | add {f g} : FiniteModes m f → FiniteModes m g → FiniteModes m (f + g)

theorem FiniteModes.finset_sum {ι : Type*} {m : ℤ} (s : Finset ι)
    (f : ι → Circle → ℂ) (h : ∀ i ∈ s, FiniteModes m (f i)) :
    FiniteModes m (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using FiniteModes.zero (m := m)
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (h i (by simp)).add (ih fun j hj => h j (by simp [hj]))

/-- Pointwise products add the lower Fourier bounds, including when either
bound is negative. -/
theorem FiniteModes.mul {m n : ℤ} {f g : Circle → ℂ}
    (hf : FiniteModes m f) (hg : FiniteModes n g) : FiniteModes (m + n) (f * g) := by
  induction hf with
  | zero => simpa using FiniteModes.zero (m := m + n)
  | add _ _ ih₁ ih₂ => simpa only [add_mul] using ih₁.add ih₂
  | mode k hk a =>
    induction hg with
    | zero => simpa using FiniteModes.zero (m := m + n)
    | add _ _ ih₁ ih₂ => simpa only [mul_add] using ih₁.add ih₂
    | mode l hl b =>
      convert FiniteModes.mode (k + l) (add_le_add hk hl) (a * b) using 1
      ext w
      simp only [Pi.mul_apply, character_add]
      ring

/-- Lower frequency bound applied entrywise to a matrix field on the circle. -/
def MatrixModes {ι κ : Type*} (m : ℤ) (F : Circle → Matrix ι κ ℂ) : Prop :=
  ∀ i j, FiniteModes m (fun w => F w i j)

theorem MatrixModes.mul {ι κ ν : Type*} [Fintype κ] {m n : ℤ}
    {F : Circle → Matrix ι κ ℂ} {G : Circle → Matrix κ ν ℂ}
    (hF : MatrixModes m F) (hG : MatrixModes n G) :
    MatrixModes (m + n) (fun w => F w * G w) := by
  intro i j
  let summand := fun k : κ => (fun w => F w i k) * (fun w => G w k j)
  have hsum := FiniteModes.finset_sum Finset.univ summand
    (fun k _ => (hF i k).mul (hG k j))
  convert hsum using 1
  funext w
  simp [Matrix.mul_apply, Finset.sum_apply, summand]

theorem holomorphic_mul {ι κ ν : Type*} [Fintype κ]
    {F : Circle → Matrix ι κ ℂ} {G : Circle → Matrix κ ν ℂ}
    (hF : MatrixModes 0 F) (hG : MatrixModes 0 G) :
    MatrixModes 0 (fun w => F w * G w) := hF.mul hG

theorem attenuation_mul_holomorphic {ι κ ν : Type*} [Fintype κ]
    {A : Circle → Matrix ι κ ℂ} {F : Circle → Matrix κ ν ℂ}
    (hA : MatrixModes (-1) A) (hF : MatrixModes 0 F) :
    MatrixModes (-1) (fun w => A w * F w) := hA.mul hF

theorem holomorphic_mul_attenuation {ι κ ν : Type*} [Fintype κ]
    {F : Circle → Matrix ι κ ℂ} {A : Circle → Matrix κ ν ℂ}
    (hF : MatrixModes 0 F) (hA : MatrixModes (-1) A) :
    MatrixModes (-1) (fun w => F w * A w) := hF.mul hA

/-- Directional derivative along the straight geodesic of unit velocity `w`. -/
def flatX (f : ℂ → Circle → ℂ) (z : ℂ) (w : Circle) : ℂ :=
  fderiv ℝ (fun p => f p w) z w

/-- The two Wirtinger components of a real-linear map on a unit velocity. -/
theorem linear_split (L : ℂ →L[ℝ] ℂ) (w : Circle) :
    L (w : ℂ) = (L 1 / 2 + L I / (2 * I)) * (w : ℂ) +
      (L 1 / 2 - L I / (2 * I)) * (w : ℂ)⁻¹ := by
  have hv : (w : ℂ) = (w : ℂ).re • (1 : ℂ) + (w : ℂ).im • I := by
    simp only [Complex.real_smul, mul_one, Complex.re_add_im]
  calc
    L (w : ℂ) = (w : ℂ).re • L 1 + (w : ℂ).im • L I := by
      conv_lhs => rw [hv, map_add, map_smul, map_smul]
    _ = _ := by
      rw [Complex.real_smul, Complex.real_smul, Complex.re_eq_add_conj,
        Complex.im_eq_sub_conj, ← Circle.coe_inv_eq_conj, Circle.coe_inv]
      ring

/-- In a mode with differentiable base coefficient, the geodesic field
creates only the two frequencies `k+1` and `k-1`. -/
theorem flatX_mode (a : ℂ → ℂ) (z : ℂ) (ha : DifferentiableAt ℝ a z)
    (k : ℤ) (w : Circle) :
    flatX (fun p v => a p * character k v) z w =
      (fderiv ℝ a z 1 / 2 + fderiv ℝ a z I / (2 * I)) * character (k + 1) w +
      (fderiv ℝ a z 1 / 2 - fderiv ℝ a z I / (2 * I)) * character (k + (-1)) w := by
  rw [flatX, fderiv_mul_const ha, ContinuousLinearMap.smul_apply,
    smul_eq_mul, linear_split (fderiv ℝ a z) w, character_add, character_add]
  simp only [character, zpow_one, zpow_neg_one]
  ring

/-- For any finite expansion with lower bound `m`, differentiation along
the Euclidean geodesic flow lowers the bound by at most one. -/
theorem flatX_sum_modes (s : Finset ℤ) (a : ℤ → ℂ → ℂ) (z : ℂ) (m : ℤ)
    (hfreq : ∀ k ∈ s, m ≤ k) (hdiff : ∀ k ∈ s, DifferentiableAt ℝ (a k) z) :
    FiniteModes (m - 1)
      (flatX (fun p w => ∑ k ∈ s, a k p * character k w) z) := by
  let term := fun k : ℤ => flatX (fun p w => a k p * character k w) z
  have hterm (k : ℤ) (hk : k ∈ s) : FiniteModes (m - 1) (term k) := by
    have hk' := hfreq k hk
    have h := (FiniteModes.mode (k + 1) (show m - 1 ≤ k + 1 by omega)
        (fderiv ℝ (a k) z 1 / 2 + fderiv ℝ (a k) z I / (2 * I))).add
      (FiniteModes.mode (k + (-1)) (show m - 1 ≤ k + (-1) by omega)
        (fderiv ℝ (a k) z 1 / 2 - fderiv ℝ (a k) z I / (2 * I)))
    convert h using 1
    funext w
    exact flatX_mode (a k) z (hdiff k hk) k w
  convert FiniteModes.finset_sum s term hterm using 1
  funext w
  simp only [flatX, Finset.sum_apply, term]
  rw [fderiv_fun_sum (fun k hk => (hdiff k hk).mul_const (character k w))]
  simp

/-- The degree threshold used for attenuations is exactly the one obtained
from finite fiberwise holomorphic polynomials under straight transport. -/
theorem flatX_holomorphic (s : Finset ℕ) (a : ℕ → ℂ → ℂ) (z : ℂ)
    (hdiff : ∀ k ∈ s, DifferentiableAt ℝ (a k) z) :
    FiniteModes (-1) (flatX (fun p w => ∑ k ∈ s, a k p * (w : ℂ) ^ k) z) := by
  let t : Finset ℤ := s.map Nat.castEmbedding
  have bound : ∀ k ∈ t, (0 : ℤ) ≤ k := by
    intro k hk
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hk
    exact Int.natCast_nonneg i
  have diff : ∀ k ∈ t, DifferentiableAt ℝ (a k.toNat) z := by
    intro k hk
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hk
    simpa using hdiff i hi
  have h := flatX_sum_modes t (fun k => a k.toNat) z 0 bound diff
  simpa [t, character, Finset.sum_map] using h

end TransportOkaGrauert.Fourier
