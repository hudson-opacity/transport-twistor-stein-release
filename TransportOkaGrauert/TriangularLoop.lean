import TransportOkaGrauert.ExteriorChange

/-!
# The Fourier mean criterion for triangular velocity loops

Splitting the absolutely convergent angular Fourier series at frequency zero
gives holomorphic upper shears on the interior and exterior disks. Their
middle coefficient is the normalized Haar mean of the original loop entry.
-/
noncomputable section
namespace TransportOkaGrauert.TriangularLoop

open Metric Complex
open scoped Matrix ContDiff

local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

/-- The Haar coefficients of the angular pullback of a circle function. -/
def coeff (h : Circle → ℂ) (k : ℤ) : ℂ :=
  fourierCoeff (fun θ : DiskSeries.Angle => h θ.toCircle) k

def series (a : ℕ → ℂ) (w : ℂ) : ℂ := ∑' n, a n * w ^ n

private theorem series_bound (a : ℕ → ℂ) (n : ℕ) {w : ℂ} (hw : w ∈ closedBall 0 1) :
    ‖a n * w ^ n‖ ≤ ‖a n‖ := by
  rw [norm_mul, norm_pow]
  exact mul_le_of_le_one_right (norm_nonneg _)
    (pow_le_one₀ (norm_nonneg _) (mem_closedBall_zero_iff.mp hw))

private theorem series_regular (a : ℕ → ℂ) (ha : Summable (fun n => ‖a n‖)) :
    DiffContOnCl ℂ (series a) (ball 0 1) := by
  have each (n : ℕ) : Differentiable ℂ (fun w : ℂ => a n * w ^ n) :=
    (differentiable_id.pow _).const_mul _
  exact DiffContOnCl.mk_ball
    (differentiableOn_tsum_of_summable_norm ha (fun n => (each n).differentiableOn)
      isOpen_ball (fun n _ hw => series_bound a n (ball_subset_closedBall hw)))
    (continuousOn_tsum (fun n => (each n).continuous.continuousOn) ha
      (fun n _ hw => series_bound a n hw))

private theorem series_hasSum (a : ℕ → ℂ) (ha : Summable (fun n => ‖a n‖))
    {w : ℂ} (hw : w ∈ closedBall 0 1) :
    HasSum (fun n => a n * w ^ n) (series a w) :=
  (ha.of_norm_bounded (fun n => series_bound a n hw)).hasSum

def positive (h : Circle → ℂ) : ℂ → ℂ := series (fun n => coeff h ((n : ℤ) + 1))

def negative (h : Circle → ℂ) : ℂ → ℂ := series (fun n => coeff h (-((n : ℤ) + 1)))

/-- The positive and negative Fourier tails, after removing one velocity or
one reciprocal velocity, extend holomorphically to the closed disks. -/
theorem half_series_spec (h : Circle → ℂ) (hc : Continuous h)
    (hs : Summable (fun k => ‖coeff h k‖)) :
    DiffContOnCl ℂ (positive h) (ball 0 1) ∧ DiffContOnCl ℂ (negative h) (ball 0 1) ∧
      ∀ v : Circle, h v = (v : ℂ) * positive h v + coeff h 0 + (v : ℂ)⁻¹ * negative h (v : ℂ)⁻¹ := by
  let pos (n : ℕ) := coeff h ((n : ℤ) + 1)
  let neg (n : ℕ) := coeff h (-((n : ℤ) + 1))
  have hp : Summable (fun n => ‖pos n‖) :=
    hs.comp_injective (show Function.Injective (fun n : ℕ => (n : ℤ) + 1) by
      intro i j hh; dsimp only at hh; omega)
  have hn : Summable (fun n => ‖neg n‖) :=
    hs.comp_injective (show Function.Injective (fun n : ℕ => -((n : ℤ) + 1)) by
      intro i j hh; dsimp only at hh; omega)
  refine ⟨series_regular pos hp, series_regular neg hn, ?_⟩
  intro v
  let θ : DiskSeries.Angle := (Complex.arg (v : ℂ) : ℝ)
  have hθ : θ.toCircle = v := (ChartModes.toCircle_angle _).trans (Circle.exp_arg v)
  let f : C(DiskSeries.Angle,ℂ) := ⟨fun t => h t.toCircle, hc.comp AddCircle.continuous_toCircle⟩
  let term (k : ℤ) := coeff h k * (v : ℂ) ^ k
  have hfour (k : ℤ) : fourier k θ = (v : ℂ) ^ k := by
    simp [fourier_apply, AddCircle.toCircle_zsmul, hθ]
  have hsum : HasSum term (h v) := by
    simpa only [f, ContinuousMap.coe_mk, smul_eq_mul, hθ, hfour, coeff, term] using
      (has_pointwise_sum_fourier_series_of_summable (f := f) hs.of_norm θ)
  have hpos : HasSum (fun n : ℕ => term ((n : ℤ) + 1)) ((v : ℂ) * series pos v) := by
    have H := (series_hasSum pos hp (w := (v : ℂ)) (by simp [mem_closedBall])).mul_left (v : ℂ)
    simpa only [term, pos, zpow_add₀ v.coe_ne_zero, zpow_natCast, zpow_one, mul_left_comm,
      mul_comm, mul_assoc] using H
  have hneg : HasSum (fun n : ℕ => term (-((n : ℤ) + 1)))
      ((v : ℂ)⁻¹ * series neg (v : ℂ)⁻¹) := by
    have H := (series_hasSum neg hn (w := (v : ℂ)⁻¹) (by simp [mem_closedBall])).mul_left (v : ℂ)⁻¹
    simpa only [term, neg, zpow_neg, zpow_add₀ v.coe_ne_zero, zpow_natCast, zpow_one, mul_inv,
      inv_pow, mul_left_comm, mul_comm, mul_assoc] using H
  simpa [term] using hsum.unique (HasSum.of_add_one_of_neg_add_one (f := term) hpos hneg)

theorem fourier_split (h : Circle → ℂ) (hc : Continuous h)
    (hs : Summable (fun k => ‖coeff h k‖)) :
    ∃ a b : ℂ → ℂ, DiffContOnCl ℂ a (ball 0 1) ∧ DiffContOnCl ℂ b (ball 0 1) ∧
      ∀ v : Circle, h v = (v : ℂ) * a v + coeff h 0 + (v : ℂ)⁻¹ * b (v : ℂ)⁻¹ :=
  ⟨positive h, negative h, half_series_spec h hc hs⟩

open BirkhoffCell

/-- In the Wiener class the off-diagonal Haar mean detects the canonical
Birkhoff cell, for an arbitrary complex boundary profile. -/
theorem bigCell_iff_of_summable (h : Circle → ℂ) (hc : Continuous h)
    (hs : Summable (fun k => ‖coeff h k‖)) :
    BigCell (fun v => standard (h v) v) ↔ coeff h 0 ≠ 0 := by
  obtain ⟨a, b, ha, hb, he⟩ := fourier_split h hc hs
  let S := upperFactor a ha
  let T := upperFactor b hb
  have eqLoop : (fun v : Circle => standard (h v) v) =
      fun v : Circle => T.val (v : ℂ)⁻¹ * (standard (coeff h 0) v * S.val v) := by
    funext v
    ext i j
    fin_cases i <;> fin_cases j <;> simp [S, T, standard, upperFactor, upperShear, Matrix.mul_apply,
      Fin.sum_univ_two]
    simpa only [add_comm, add_left_comm, add_assoc, mul_comm] using he v
  rw [eqLoop, bigCell_left_iff (fun v => standard (coeff h 0) v * S.val v) T,
    bigCell_right_iff (fun v => standard (coeff h 0) v) S, standard_big_iff]

/-- Two derivatives in the angular variable imply the required absolute
summability, so the mean criterion applies in particular to smooth loops. -/
theorem bigCell_iff (h : Circle → ℂ) (smooth : ContDiff ℝ 2 (fun t : ℝ => h (Circle.exp t))) :
    BigCell (fun v => standard (h v) v) ↔ coeff h 0 ≠ 0 := by
  apply bigCell_iff_of_summable
  · exact Circle.isAddQuotientCoveringMap_exp.isOpenQuotientMap.isQuotientMap.continuous_iff.mpr
      smooth.continuous
  · apply FourierDecay.summable_fourierCoeff_norm (fun θ : DiskSeries.Angle => h θ.toCircle)
    simpa only [ChartModes.toCircle_angle] using smooth

end TransportOkaGrauert.TriangularLoop
