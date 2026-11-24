import TransportOkaGrauert.FlatMatrix
import TransportOkaGrauert.BoundaryModes
import TransportOkaGrauert.FourierDecay
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Data.Matrix.Basis

/-!
# Infinite Fourier profiles on the flat disk

For a continuous angular profile with absolutely summable Fourier coefficients
in frequencies ≥ −1, multiply by the unit velocity and reconstruct the
resulting holomorphic disk function by its power series. The construction
works entrywise for arbitrary finite matrix rank.
-/

namespace TransportOkaGrauert.DiskSeries

noncomputable section
open Complex Metric Real FlatMatrix
open scoped ComplexConjugate Matrix.Norms.Operator Real ContDiff

abbrev Angle := AddCircle (2 * π)
local instance : Fact (0 < 2 * π) := ⟨two_pi_pos⟩

/-- The compensated power series. Negative exponents below −1 are assigned
power zero; the admissibility assumption makes their coefficients vanish. -/
def series (a : C(Angle, ℂ)) (w : ℂ) : ℂ :=
  ∑' k : ℤ, fourierCoeff a k * w ^ (k + 1).toNat

theorem series_regular (a : C(Angle, ℂ)) (h : Summable (fun k : ℤ => ‖fourierCoeff a k‖)) :
    DiffContOnCl ℂ (series a) (ball 0 1) := by
  have bound (k : ℤ) (w : ℂ) (hw : w ∈ closedBall 0 1) :
      ‖fourierCoeff a k * w ^ (k + 1).toNat‖ ≤ ‖fourierCoeff a k‖ := by
    rw [norm_mul, norm_pow]
    exact mul_le_of_le_one_right (norm_nonneg _)
      (pow_le_one₀ (norm_nonneg _) (mem_closedBall_zero_iff.mp hw))
  have each (k : ℤ) : Differentiable ℂ (fun w : ℂ => fourierCoeff a k * w ^ (k + 1).toNat) :=
    (differentiable_id.pow _).const_mul _
  exact DiffContOnCl.mk_ball
    (differentiableOn_tsum_of_summable_norm h (fun k => (each k).differentiableOn)
      isOpen_ball (fun k w hw => bound k w (ball_subset_closedBall hw)))
    (continuousOn_tsum (fun k => (each k).continuous.continuousOn) h bound)

/-- Recover the prescribed attenuation on the actual angle circle from its
own Haar Fourier coefficients. -/
theorem series_boundary (a : C(Angle, ℂ)) (h : Summable (fun k : ℤ => ‖fourierCoeff a k‖))
    (support : ∀ k : ℤ, k < -1 → fourierCoeff a k = 0) (θ : Angle) :
    conj (θ.toCircle : ℂ) * series a θ.toCircle = a θ := by
  have power (k : ℤ) (hk : -1 ≤ k) :
      (θ.toCircle : ℂ) ^ (k + 1).toNat = fourier k θ * (θ.toCircle : ℂ) := by
    have hk' : 0 ≤ k + 1 := by omega
    rw [← zpow_natCast, Int.toNat_of_nonneg hk', zpow_add₀ θ.toCircle.coe_ne_zero, zpow_one]
    simp [fourier_apply, AddCircle.toCircle_zsmul]
  have terms (k : ℤ) :
      fourierCoeff a k * (θ.toCircle : ℂ) ^ (k + 1).toNat =
      (fourierCoeff a k • fourier k θ) * (θ.toCircle : ℂ) := by
    by_cases hk : -1 ≤ k
    · rw [power k hk, smul_eq_mul, mul_assoc]
    · simp [support k (by omega)]
  have eqn : series a θ.toCircle = a θ * (θ.toCircle : ℂ) := by
    simpa only [series, terms] using
      ((has_pointwise_sum_fourier_series_of_summable (f := a) h.of_norm θ).mul_right
        (θ.toCircle : ℂ)).tsum_eq
  rw [eqn, ← Circle.coe_inv_eq_conj, Circle.coe_inv, mul_comm _ (a θ * _),
    mul_assoc, mul_inv_cancel₀ θ.toCircle.coe_ne_zero, mul_one]

/-- For twice differentiable boundary data, the cutoff at −1 is equivalent
to a holomorphic disk extension after multiplication by the velocity. -/
theorem admissible_iff_diskExtension (a : C(Angle, ℂ))
    (smooth : ContDiff ℝ 2 (fun t : ℝ => a (t : Angle))) :
    (∀ k : ℤ, k < -1 → fourierCoeff a k = 0) ↔
      ∃ b : ℂ → ℂ, DiffContOnCl ℂ b (ball 0 1) ∧
        ∀ θ : Angle, conj (θ.toCircle : ℂ) * b θ.toCircle = a θ := by
  constructor
  · intro support
    have hs := FourierDecay.summable_fourierCoeff_norm a smooth
    exact ⟨series a, series_regular a hs, series_boundary a hs support⟩
  · rintro ⟨b, hb, trace⟩ k hk
    have he : (a : Angle → ℂ) = fun θ =>
        conj (θ.toCircle : ℂ) * BoundaryModes.boundaryTrace b θ := funext fun θ => (trace θ).symm
    rw [he, BoundaryModes.conjugate_shift]
    exact BoundaryModes.negativeMode_eq_zero hb _ (by omega)

variable {n : ℕ}

/-- A matrix entry, retained as a continuous function on the compact angle
circle so that the Fourier inversion theorem applies. -/
def entry (a : C(Angle, Mat n)) (i j : Fin n) : C(Angle, ℂ) :=
  ⟨fun θ => a θ i j, (continuous_apply j).comp ((continuous_apply i).comp a.continuous)⟩

def matrixSeries (a : C(Angle, Mat n)) (w : ℂ) : Mat n :=
  ∑ i, ∑ j, series (entry a i j) w • Matrix.single i j 1

theorem matrixSeries_regular (a : C(Angle, Mat n))
    (hs : ∀ i j, Summable (fun k : ℤ => ‖fourierCoeff (entry a i j) k‖)) :
    DiffContOnCl ℂ (matrixSeries a) (ball 0 1) := by
  have h i j := (series_regular (entry a i j) (hs i j)).smul_const
    (Matrix.single i j (1 : ℂ))
  exact ⟨DifferentiableOn.fun_sum fun i _ => DifferentiableOn.fun_sum fun j _ =>
      (h i j).differentiableOn,
    continuousOn_finset_sum _ fun i _ => continuousOn_finset_sum _ fun j _ => (h i j).continuousOn⟩

theorem matrixSeries_boundary (a : C(Angle, Mat n))
    (hs : ∀ i j, Summable (fun k : ℤ => ‖fourierCoeff (entry a i j) k‖))
    (support : ∀ i j (k : ℤ), k < -1 → fourierCoeff (entry a i j) k = 0) (θ : Angle) :
    attenuation (matrixSeries a) θ.toCircle = a θ := by
  simp only [attenuation, matrixSeries, Finset.smul_sum,
    series_boundary _ (hs _ _) (support _ _) θ, Matrix.smul_single, smul_eq_mul, mul_one]
  exact Matrix.sum_sum_single _

/-- The compensated boundary value is the original matrix times the unit
direction. This identity transfers smoothness from the prescribed boundary
data directly to the integrating factors on the unit tangent bundle. -/
theorem matrixSeries_trace (a : C(Angle, Mat n))
    (hs : ∀ i j, Summable (fun k : ℤ => ‖fourierCoeff (entry a i j) k‖))
    (support : ∀ i j (k : ℤ), k < -1 → fourierCoeff (entry a i j) k = 0) (θ : Angle) :
    matrixSeries a θ.toCircle = (θ.toCircle : ℂ) • a θ := by
  have he := congrArg (fun M : Mat n => (θ.toCircle : ℂ) • M)
    (matrixSeries_boundary a hs support θ)
  simpa only [attenuation, smul_smul, ← Circle.coe_inv_eq_conj, Circle.coe_inv,
    mul_inv_cancel₀ θ.toCircle.coe_ne_zero, one_smul] using he

theorem factors_regular (a : C(Angle, Mat n))
    (hs : ∀ i j, Summable (fun k : ℤ => ‖fourierCoeff (entry a i j) k‖)) (z : ℂ) :
    DiffContOnCl ℂ (factor (matrixSeries a) z) (ball 0 1) ∧
    DiffContOnCl ℂ (inverseFactor (matrixSeries a) z) (ball 0 1) := by
  have h := matrixSeries_regular a hs
  have hd := factors_holomorphicOn (matrixSeries a) h.differentiableOn z
  have he : Continuous (NormedSpace.exp : Mat n → Mat n) := NormedSpace.exp_continuous
  exact ⟨⟨hd.1, he.comp_continuousOn (h.continuousOn.const_smul _)⟩,
    ⟨hd.2, he.comp_continuousOn (h.continuousOn.const_smul _)⟩⟩

/-- Smoothness of the frames on the unit tangent bundle uses the angle as a
periodic real coordinate. -/
theorem factors_smooth_boundary (a : C(Angle, Mat n))
    (smooth : ContDiff ℝ ∞ (fun t : ℝ => a (t : Angle)))
    (hs : ∀ i j, Summable (fun k : ℤ => ‖fourierCoeff (entry a i j) k‖))
    (support : ∀ i j (k : ℤ), k < -1 → fourierCoeff (entry a i j) k = 0) :
    ContDiff ℝ ∞ (fun p : ℂ × ℝ => factor (matrixSeries a) p.1 (AddCircle.toCircle (p.2 : Angle))) ∧
    ContDiff ℝ ∞ (fun p : ℂ × ℝ => inverseFactor (matrixSeries a) p.1 (AddCircle.toCircle (p.2 : Angle))) := by
  have hc : ContDiff ℝ ∞ (fun p : ℂ × ℝ => conj p.1) :=
    Complex.conjCLE.contDiff.comp contDiff_fst
  have hw : ContDiff ℝ ∞ (fun p : ℂ × ℝ => ((AddCircle.toCircle (p.2 : Angle)) : ℂ)) := by
    simpa [AddCircle.toCircle, circleMap, Function.comp_def] using (contDiff_circleMap 0 1).comp
      (contDiff_snd : ContDiff ℝ ∞ (fun p : ℂ × ℝ => p.2))
  have he : ContDiff ℝ ∞ (NormedSpace.exp : Mat n → Mat n) :=
    contDiff_iff_contDiffAt.mpr fun _ => (NormedSpace.exp_analytic (𝕂 := ℝ) _).contDiffAt
  simp only [factor, inverseFactor, matrixSeries_trace a hs support]
  exact ⟨he.comp (hc.neg.smul (hw.smul (smooth.comp contDiff_snd))),
    he.comp (hc.smul (hw.smul (smooth.comp contDiff_snd)))⟩

/-- Holomorphic integrating factors in the boundary-smooth category. The disk
extension also certifies the one-sided angular Fourier support. -/
def HasIntegratingFactor (a : Angle → Mat n) : Prop :=
    ∃ F G : ℂ → ℂ → Mat n,
      (ContDiff ℝ ∞ (fun p : ℂ × ℝ => F p.1 (AddCircle.toCircle (p.2 : Angle))) ∧
       ContDiff ℝ ∞ (fun p : ℂ × ℝ => G p.1 (AddCircle.toCircle (p.2 : Angle)))) ∧
      (∀ z, DiffContOnCl ℂ (F z) (ball 0 1) ∧ DiffContOnCl ℂ (G z) (ball 0 1)) ∧
      (∀ z k, k < 0 →
        fourierCoeff (BoundaryModes.boundaryTrace (F z)) k = 0 ∧
        fourierCoeff (BoundaryModes.boundaryTrace (G z)) k = 0) ∧
      (∀ z w, F z w * G z w = 1 ∧ G z w * F z w = 1) ∧
      ∀ z (θ : Angle), HasDerivAt (fun t : ℝ => F (z + t * (θ.toCircle : ℂ)) θ.toCircle)
        (-(a θ * F z θ.toCircle)) 0

/-- Smoothness of the periodic angular lift is inherited by each scalar entry. -/
theorem entry_smooth (a : C(Angle, Mat n)) (smooth : ContDiff ℝ ∞ (fun t : ℝ => a (t : Angle)))
    (i j : Fin n) : ContDiff ℝ ∞ (fun t : ℝ => entry a i j (t : Angle)) := by
  let ev : Mat n →L[ℝ] ℂ :=
    ⟨Matrix.entryLinearMap ℝ ℂ i j, (continuous_apply j).comp (continuous_apply i)⟩
  exact ev.contDiff.comp smooth

/-- The two smooth boundary frames have no negative angular modes and solve
the geodesic transport equation for the originally prescribed attenuation. -/
theorem integratingFactor_of_summable (a : C(Angle, Mat n))
    (smooth : ContDiff ℝ ∞ (fun t : ℝ => a (t : Angle)))
    (hs : ∀ i j, Summable (fun k : ℤ => ‖fourierCoeff (entry a i j) k‖))
    (support : ∀ i j (k : ℤ), k < -1 → fourierCoeff (entry a i j) k = 0) :
    HasIntegratingFactor a := by
  refine ⟨factor (matrixSeries a), inverseFactor (matrixSeries a),
    factors_smooth_boundary a smooth hs support, factors_regular a hs, ?_,
    factor_inverses (matrixSeries a), ?_⟩
  · intro z k hk
    obtain ⟨hF, hG⟩ := factors_regular a hs z
    exact ⟨BoundaryModes.negativeMode_eq_zero hF k hk, BoundaryModes.negativeMode_eq_zero hG k hk⟩
  · intro z θ
    simpa only [matrixSeries_boundary a hs support θ] using
      factor_transport (matrixSeries a) z θ.toCircle

/-- Transport Oka–Grauert integrating factors on a Euclidean disk for every
smooth, position-independent matrix attenuation whose angular Fourier
coefficients vanish below −1. No summability or analyticity is assumed. -/
theorem smooth_directionOnlyIntegratingFactor (a : C(Angle, Mat n))
    (smooth : ContDiff ℝ ∞ (fun t : ℝ => a (t : Angle)))
    (support : ∀ i j (k : ℤ), k < -1 → fourierCoeff (entry a i j) k = 0) :
    HasIntegratingFactor a :=
  integratingFactor_of_summable a smooth (fun i j =>
    FourierDecay.summable_fourierCoeff_norm (entry a i j) ((entry_smooth a smooth i j).of_le (by decide)))
    support

end
end TransportOkaGrauert.DiskSeries
