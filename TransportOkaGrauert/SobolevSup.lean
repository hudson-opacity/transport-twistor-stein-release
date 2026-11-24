import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Normed

/-!
# A Euclidean H² to uniform estimate in three dimensions

With mathlib's Fourier normalization, use the weight `1 + ‖ξ‖²` to
measure two derivatives. The inverse weight is square integrable in
dimension three. Hölder's inequality gives an integrable Fourier transform
and inversion then bounds the value at every continuity point. The target
may be any complete complex normed space.
-/
noncomputable section
namespace TransportOkaGrauert.SobolevSup
open MeasureTheory Real Module
open scoped FourierTransform ENNReal RealInnerProductSpace SchwartzMap

abbrev Space := EuclideanSpace ℝ (Fin 3)

/-- Fourier weight of the inhomogeneous H² norm used here. -/
def weight (ξ : Space) : ℝ := 1 + ‖ξ‖ ^ 2

theorem weight_pos (ξ : Space) : 0 < weight ξ := by unfold weight; positivity

/-- The embedding constant is the finite L² norm of the inverse weight. -/
def constant : ℝ := √(∫ ξ : Space, (weight ξ)⁻¹ ^ 2)

theorem inverseWeight_memLp : MemLp (fun ξ : Space => (weight ξ)⁻¹) 2 volume := by
  have hc : Continuous (fun ξ : Space => (weight ξ)⁻¹) :=
    (continuous_const.add (continuous_norm.pow 2)).inv₀ fun ξ => (weight_pos ξ).ne'
  apply (memLp_two_iff_integrable_sq hc.aestronglyMeasurable).2
  have hd : (finrank ℝ Space : ℝ) < (4 : ℝ) := by rw [finrank_euclideanSpace_fin]; norm_num
  have h := integrable_rpow_neg_one_add_norm_sq (μ := (volume : Measure Space)) hd
  convert h using 1
  funext ξ
  change (1 + ‖ξ‖ ^ 2)⁻¹ ^ 2 = _
  rw [show -(4:ℝ) / 2 = -(2:ℝ) by norm_num, Real.rpow_neg (by positivity)]
  norm_num

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Fourier definition of the two-derivative size. -/
def hTwoSize (f : Space → E) : ℝ := √(∫ ξ, (weight ξ * ‖𝓕 f ξ‖) ^ 2)

/-- Finite weighted Fourier L² energy. -/
def FiniteHTwo (f : Space → E) : Prop :=
  MemLp (fun ξ => weight ξ * ‖𝓕 f ξ‖) 2 volume

private theorem fourier_l1 {f : Space → E} (hf : Integrable f) (h2 : FiniteHTwo f) :
    Integrable (𝓕 f) := by
  have hcont : Continuous (𝓕 f) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      ((innerSL ℝ (E := Space)).continuous₂) hf
  apply (integrable_norm_iff hcont.aestronglyMeasurable).mp
  have h := inverseWeight_memLp.integrable_mul h2
  convert h using 1
  funext ξ
  change ‖𝓕 f ξ‖ = (weight ξ)⁻¹ * (weight ξ * ‖𝓕 f ξ‖)
  rw [inv_mul_cancel_left₀ (weight_pos ξ).ne']

/-- Cauchy–Schwarz with the inverse Japanese-bracket weight gives the actual
finite constant in the L¹ bound of the transform. -/
theorem integral_fourier_norm_le {f : Space → E} (h2 : FiniteHTwo f) :
    (∫ ξ, ‖𝓕 f ξ‖) ≤ constant * hTwoSize f := by
  have hx : 0 ≤ᵐ[volume] fun ξ : Space => (weight ξ)⁻¹ :=
    Filter.Eventually.of_forall fun ξ => inv_nonneg.mpr (weight_pos ξ).le
  have hy : 0 ≤ᵐ[volume] fun ξ => weight ξ * ‖𝓕 f ξ‖ :=
    Filter.Eventually.of_forall fun ξ => mul_nonneg (weight_pos ξ).le (norm_nonneg _)
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two hx hy
    (by simpa using inverseWeight_memLp) (by simpa using h2)
  have hc (ξ : Space) : (weight ξ)⁻¹ * (weight ξ * ‖𝓕 f ξ‖) = ‖𝓕 f ξ‖ :=
    inv_mul_cancel_left₀ (weight_pos ξ).ne' _
  simpa only [hc, constant, hTwoSize, Real.rpow_two, Real.sqrt_eq_rpow, one_div] using h

/-- The Euclidean H²→C⁰ bound, pointwise at every continuity point of an
integrable representative. Fourier integrability is a consequence. -/
theorem pointwise_bound [CompleteSpace E] {f : Space → E} (hf : Integrable f) (h2 : FiniteHTwo f)
    {x : Space} (hx : ContinuousAt f x) : ‖f x‖ ≤ constant * hTwoSize f := by
  calc
    ‖f x‖ = ‖𝓕⁻ (𝓕 f) x‖ := congrArg norm (hf.fourierInv_fourier_eq (fourier_l1 hf h2) hx).symm
    _ ≤ ∫ ξ, ‖𝓕 f ξ‖ := by
      rw [Real.fourierInv_eq]
      simpa only [Circle.norm_smul] using norm_integral_le_integral_norm
        (fun ξ : Space => Real.fourierChar (inner ℝ ξ x) • 𝓕 f ξ)
    _ ≤ _ := integral_fourier_norm_le h2

/-- Rapid decay of the Schwartz transform automatically supplies finite
two-derivative energy. -/
theorem finiteHTwo_schwartz (f : 𝓢(Space, E)) : FiniteHTwo (f : Space → E) := by
  let G : 𝓢(Space, E) := 𝓕 f
  change MemLp (fun ξ => weight ξ * ‖G ξ‖) 2 volume
  have hc : Continuous (fun ξ => weight ξ * ‖G ξ‖) :=
    (continuous_const.add (continuous_norm.pow 2)).mul G.continuous.norm
  apply (memLp_two_iff_integrable_sq hc.aestronglyMeasurable).mpr
  let C := (SchwartzMap.seminorm ℝ 0 0) G
  have bound : Integrable (fun ξ => C *
      ((‖ξ‖ ^ 0 * ‖G ξ‖ + 2 * (‖ξ‖ ^ 2 * ‖G ξ‖)) + ‖ξ‖ ^ 4 * ‖G ξ‖)) volume :=
    (((G.integrable_pow_mul volume 0).add ((G.integrable_pow_mul volume 2).const_mul 2)).add
      (G.integrable_pow_mul volume 4)).const_mul C
  apply bound.mono' (hc.pow 2).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro ξ
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  calc
    _ = (weight ξ ^ 2 * ‖G ξ‖) * ‖G ξ‖ := by ring
    _ ≤ (weight ξ ^ 2 * ‖G ξ‖) * C :=
      mul_le_mul_of_nonneg_left (G.norm_le_seminorm ℝ ξ) (by positivity)
    _ = _ := by unfold weight; ring

/-- Every Schwartz section on Euclidean three-space satisfies the bound. -/
theorem schwartz_bound [CompleteSpace E] (f : 𝓢(Space, E)) (x : Space) :
    ‖f x‖ ≤ constant * hTwoSize (f : Space → E) :=
  pointwise_bound f.integrable (finiteHTwo_schwartz f) f.continuous.continuousAt

section Matrix

open scoped Matrix.Norms.Operator NNReal

private theorem opNorm_le_of_rows {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ)
    {R : ℝ} (hR : 0 ≤ R) (hrow : ∀ i, ∑ j, ‖M i j‖ ≤ R) : ‖M‖ ≤ R := by
  rw [Matrix.linfty_opNorm_def]
  let B : ℝ≥0 := ⟨R, hR⟩
  change ((Finset.univ.sup fun i => ∑ j, ‖M i j‖₊ : ℝ≥0) : ℝ) ≤ (B : ℝ)
  apply NNReal.coe_le_coe.mpr
  apply Finset.sup_le
  intro i _
  apply NNReal.coe_le_coe.mp
  simpa [B, NNReal.coe_sum] using hrow i

/-- Uniform entrywise control yields the chart's maximum-row-sum
operator norm, with factor n. Includes the empty matrix in rank zero. -/
theorem opNorm_le_rank_mul {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ)
    {R : ℝ} (hR : 0 ≤ R) (hentry : ∀ i j, ‖M i j‖ ≤ R) : ‖M‖ ≤ n * R := by
  apply opNorm_le_of_rows M (mul_nonneg (Nat.cast_nonneg _) hR)
  intro i
  simpa using Finset.sum_le_sum (s := Finset.univ) (fun j _ => hentry i j)

/-- Comparison with the Hilbert–Schmidt norm (the square root of the
sum of squared entry norms). Only a factor √n is needed. -/
theorem opNorm_le_sqrt_rank_mul_hilbertSchmidt {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    ‖M‖ ≤ √(n : ℝ) * √(∑ i, ∑ j, ‖M i j‖ ^ 2) := by
  apply opNorm_le_of_rows M (by positivity)
  intro i
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq (R := ℝ) Finset.univ
    (fun _ : Fin n => 1) (fun j => ‖M i j‖)
  have hrow : (∑ j, ‖M i j‖) ^ 2 ≤ (n : ℝ) * ∑ j, ‖M i j‖ ^ 2 := by simpa using hCS
  have hsub : ∑ j, ‖M i j‖ ^ 2 ≤ ∑ q, ∑ j, ‖M q j‖ ^ 2 :=
    Finset.single_le_sum (fun q _ => Finset.sum_nonneg fun j _ => sq_nonneg ‖M q j‖) (Finset.mem_univ i)
  calc
    ∑ j, ‖M i j‖ = √((∑ j, ‖M i j‖) ^ 2) := (Real.sqrt_sq (by positivity)).symm
    _ ≤ √((n : ℝ) * ∑ q, ∑ j, ‖M q j‖ ^ 2) :=
      Real.sqrt_le_sqrt (hrow.trans (mul_le_mul_of_nonneg_left hsub (Nat.cast_nonneg _)))
    _ = _ := Real.sqrt_mul (Nat.cast_nonneg _) _

/-- Direct conversion from scalar Sobolev estimates on all entries to
the matrix norm used in the gauge-inverse smallness criterion. -/
theorem matrix_schwartz_bound {n : ℕ} (f : Fin n → Fin n → 𝓢(Space, ℂ)) {R : ℝ}
    (hR : 0 ≤ R) (hentry : ∀ i j, hTwoSize ((f i j) : Space → ℂ) ≤ R) (x : Space) :
    ‖Matrix.of (fun i j => f i j x)‖ ≤ n * (constant * R) := by
  have hC : 0 ≤ constant := Real.sqrt_nonneg _
  exact opNorm_le_rank_mul _ (mul_nonneg hC hR) fun i j =>
    (schwartz_bound (f i j) x).trans (mul_le_mul_of_nonneg_left (hentry i j) hC)

end Matrix

end TransportOkaGrauert.SobolevSup
