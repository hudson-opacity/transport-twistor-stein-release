import TransportOkaGrauert.TriangularLoop
import TransportOkaGrauert.SmoothCellChange
import Mathlib.Analysis.Calculus.SmoothSeries

/-! Smooth angular traces of the two disk shears for a smooth triangular loop.
Integration by parts on the circle gives absolute summability with every
polynomial weight. This permits uniform termwise angular differentiation. -/

noncomputable section
namespace TransportOkaGrauert.SmoothTriangularLoop

open Complex Metric TriangularLoop BirkhoffCell
open scoped ContDiff
local notation "T" => (2 * Real.pi)
local instance : Fact (0 < T) := ⟨Real.two_pi_pos⟩

private theorem lift_coeff (g : ℝ → ℂ) (hp : g.Periodic T) (k : ℤ) :
    fourierCoeff hp.lift k = fourierCoeffOn Real.two_pi_pos g k := by
  rw [fourierCoeffOn_eq_integral, fourierCoeff_eq_intervalIntegral _ _ 0]
  simp [Function.Periodic.lift_coe]

private theorem weighted (d : ℕ) (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
    (hp : g.Periodic T) (k : ℕ → ℤ) (hk : Function.Injective k) (hn : ∀ n, k n ≠ 0) :
    Summable (fun n => ‖fourierCoeffOn Real.two_pi_pos g (k n)‖ * |(k n : ℝ)| ^ d) := by
  induction d generalizing g with
  | zero =>
    have hs := FourierDecay.summable_fourierCoeff_norm hp.lift (by
      simpa only [Function.Periodic.lift_coe] using hg.of_le (by decide : (2 : WithTop ℕ∞) ≤ ∞))
    simpa only [pow_zero, mul_one, lift_coeff] using hs.comp_injective hk
  | succ d ih =>
    have hg' : ContDiff ℝ ∞ (deriv g) := (show ContDiff ℝ (∞ + 1) g by simpa using hg).deriv'
    have hp' : (deriv g).Periodic T := by
      intro t
      rw [← deriv_comp_add_const, show (fun x => g (x + T)) = g from funext hp]
    convert ih (deriv g) hg' hp' using 1
    funext n
    have he : fourierCoeffOn Real.two_pi_pos (deriv g) (k n) =
        (I * (k n : ℂ)) * fourierCoeffOn Real.two_pi_pos g (k n) :=
      FourierDecay.derivative_coefficient g hp (hg.differentiable (by decide)) hg'.continuous _ (hn n)
    rw [he, norm_mul, norm_mul, norm_I, one_mul,
      Complex.norm_intCast, pow_succ]
    ring

private theorem circle_pow (n : ℕ) (t : ℝ) :
    (Circle.exp t : ℂ) ^ n = Complex.exp ((n : ℂ) * I * t) := by
  rw [Circle.coe_exp, ← Complex.exp_nat_mul]
  congr 1
  ring

private theorem wave_derivative (a c : ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => a * Complex.exp (c * s)) (a * c * Complex.exp (c * t)) t := by
  have H := (((Complex.hasDerivAt_exp (c * (t : ℂ))).comp (t : ℂ)
    ((hasDerivAt_id (t : ℂ)).const_mul c)).const_mul a).comp_ofReal
  convert H using 1
  simp [mul_comm, mul_assoc]

private theorem iterated_wave (d : ℕ) (a c : ℂ) :
    iteratedDeriv d (fun t : ℝ => a * Complex.exp (c * t)) =
      fun t : ℝ => (a * c ^ d) * Complex.exp (c * t) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    rw [(wave_derivative (a * c ^ d) c t).deriv, pow_succ]
    simp only [mul_assoc]

private theorem smooth_series (a : ℕ → ℂ)
    (ha : ∀ d : ℕ, Summable (fun n => ‖a n‖ * (n : ℝ) ^ d)) :
    ContDiff ℝ ∞ (fun t : ℝ => series a (Circle.exp t)) := by
  change ContDiff ℝ ∞ (fun t : ℝ => ∑' n : ℕ, a n * (Circle.exp t : ℂ) ^ n)
  simp only [circle_pow]
  apply contDiff_tsum (v := fun d n => ‖a n‖ * (n : ℝ) ^ d)
  · intro n
    exact contDiff_const.mul ((contDiff_const.mul Complex.ofRealCLM.contDiff).cexp)
  · intro d _; exact ha d
  · intro d n t _
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iterated_wave, norm_mul, norm_mul, norm_pow,
      norm_mul, norm_I, mul_one, norm_natCast, ← circle_pow]
    simp [norm_pow]

theorem half_series_smooth (h : Circle → ℂ)
    (smooth : ContDiff ℝ ∞ (fun t : ℝ => h (Circle.exp t))) :
    ContDiff ℝ ∞ (fun t : ℝ => positive h (Circle.exp t)) ∧
    ContDiff ℝ ∞ (fun t : ℝ => negative h (Circle.exp t)) := by
  let g (t : ℝ) := h (Circle.exp t)
  have hp : g.Periodic T := fun t => congrArg h (Circle.periodic_exp t)
  have hc (k : ℤ) : fourierCoeffOn Real.two_pi_pos g k = coeff h k := by
    rw [coeff, fourierCoeffOn_eq_integral, fourierCoeff_eq_intervalIntegral _ _ 0]
    simp [g, ChartModes.toCircle_angle]
  have from_freq (k : ℕ → ℤ) (hk : Function.Injective k) (hn : ∀ n, k n ≠ 0)
      (hle : ∀ n : ℕ, (n : ℝ) ≤ |(k n : ℝ)|) (d : ℕ) :
      Summable (fun n => ‖coeff h (k n)‖ * (n : ℝ) ^ d) := by
    have hs := weighted d g smooth hp k hk hn
    simp only [hc] at hs
    exact hs.of_nonneg_of_le (fun n => by positivity) (fun n =>
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg n) (hle n) d) (norm_nonneg _))
  constructor <;> apply smooth_series <;> intro d
  · apply from_freq (fun n => (n : ℤ) + 1) _ _ _ d
    · intro x y he; dsimp only at he; omega
    · intro n; dsimp only; omega
    · intro n
      simp only [Int.cast_add, Int.cast_natCast, Int.cast_one]
      rw [abs_of_nonneg (by positivity)]
      linarith
  · apply from_freq (fun n => -((n : ℤ) + 1)) _ _ _ d
    · intro x y he; dsimp only at he; omega
    · intro n; dsimp only; omega
    · intro n
      simp only [Int.cast_neg, abs_neg, Int.cast_add, Int.cast_natCast, Int.cast_one]
      rw [abs_of_nonneg (by positivity)]
      linarith

/-- A smooth triangular velocity loop has a smooth canonical Birkhoff
factorization precisely when its angular Haar mean is nonzero. -/
theorem smoothBigCell_iff (h : Circle → ℂ) (smooth : ContDiff ℝ ∞ (fun t : ℝ => h (Circle.exp t))) :
    BoundaryJump.SmoothBigCell (fun v => standard (h v) v) ↔ coeff h 0 ≠ 0 := by
  have hc : Continuous h :=
    Circle.isAddQuotientCoveringMap_exp.isOpenQuotientMap.isQuotientMap.continuous_iff.mpr
      smooth.continuous
  have hs : Summable (fun k => ‖coeff h k‖) := by
    apply FourierDecay.summable_fourierCoeff_norm (fun θ : DiskSeries.Angle => h θ.toCircle)
    simpa only [ChartModes.toCircle_angle] using smooth.of_le (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  obtain ⟨ha, hb, he⟩ := half_series_spec h hc hs
  obtain ⟨ha', hb'⟩ := half_series_smooth h smooth
  let S := upperFactor (positive h) ha
  let G := upperFactor (negative h) hb
  have eqLoop : (fun v : Circle => standard (h v) v) =
      fun v : Circle => G.val (v : ℂ)⁻¹ * (standard (coeff h 0) v * S.val v) := by
    funext v
    ext i j
    fin_cases i <;> fin_cases j <;> simp [S, G, standard, upperFactor, upperShear, Matrix.mul_apply,
      Fin.sum_univ_two]
    simpa only [add_comm, add_left_comm, add_assoc, mul_comm] using he v
  rw [eqLoop, SmoothCellChange.smoothBigCell_left_iff _ G (SmoothCellChange.upperFactor_smooth hb hb'),
    SmoothCellChange.smoothBigCell_right_iff _ S (SmoothCellChange.upperFactor_smooth ha ha'),
    SmoothCellChange.standard_smooth_iff]

end TransportOkaGrauert.SmoothTriangularLoop
