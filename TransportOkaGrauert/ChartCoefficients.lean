import TransportOkaGrauert.SkewReduction
import TransportOkaGrauert.CoefficientIntegral

/-! Actual Haar coefficients of the isothermal chart transport system.
The transported unknown may have infinitely many Fourier modes. -/

noncomputable section
namespace TransportOkaGrauert.ChartCoefficients
open SimpleDiskTarget SkewReduction ChartModes ChartOrbits Complex Metric MeasureTheory Real
open scoped ComplexConjugate ContDiff
local instance : Fact (0 < 2 * π) := ⟨Real.two_pi_pos⟩
abbrev Angle := DiskSeries.Angle

/-- A single angular character shifts the Haar coefficient on every profile. -/
theorem coeff_shift (f : Angle → ℂ) (k l : ℤ) :
    fourierCoeff (fun θ => fourier l θ * f θ) k = fourierCoeff f (k-l) := by
  unfold fourierCoeff
  simp only [smul_eq_mul, ← mul_assoc, ← fourier_add, neg_sub]
  rw [show -k + l = l - k by omega]

private theorem int_of_cont {f : Angle → ℂ} (h : Continuous f) :
    Integrable f AddCircle.haarAddCircle :=
  h.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

private theorem coeff_add {f g : Angle → ℂ} (hf : Continuous f) (hg : Continuous g) (k : ℤ) :
    fourierCoeff (fun θ => f θ + g θ) k = fourierCoeff f k + fourierCoeff g k := by
  exact congrFun (fourierCoeff.add (int_of_cont hf) (int_of_cont hg)) k

private theorem coeff_sum {ι : Type*} (s : Finset ι) (f : ι → Angle → ℂ) (hf : ∀ i, Continuous (f i)) (k : ℤ) :
    fourierCoeff (fun θ => ∑ i ∈ s, f i θ) k = ∑ i ∈ s, fourierCoeff (f i) k := by
  have he : (fun θ => ∑ i ∈ s, f i θ) = ∑ i ∈ s, f i := by ext θ; simp
  rw [he, fourierCoeff.sum s f (fun i _ => int_of_cont (hf i))]
  simp

private theorem poly_times (bneg b₀ bpos : ℂ) (g : Angle → ℂ) (hg : Continuous g) (k : ℤ) :
    fourierCoeff (fun θ => (conj (θ.toCircle : ℂ) * bneg + b₀ + (θ.toCircle : ℂ) * bpos) * g θ) k =
      bneg * fourierCoeff g (k+1) + b₀ * fourierCoeff g k + bpos * fourierCoeff g (k-1) := by
  have hu (l : ℤ) : Continuous fun θ : Angle => fourier l θ * g θ := (fourier l).continuous.mul hg
  have he : (fun θ : Angle => (conj (θ.toCircle : ℂ) * bneg + b₀ + (θ.toCircle : ℂ) * bpos) * g θ) =
      fun θ => (bneg * (fourier (-1) θ * g θ) + b₀ * g θ) + bpos * (fourier 1 θ * g θ) := by
    funext θ
    rw [fourier_neg (n := 1), fourier_one]; ring
  rw [he, coeff_add (f := fun θ => bneg * (fourier (-1) θ * g θ) + b₀ * g θ)
      (g := fun θ => bpos * (fourier 1 θ * g θ)) ((continuous_const.mul (hu (-1))).add (continuous_const.mul hg))
      (continuous_const.mul (hu 1)), coeff_add (f := fun θ => bneg * (fourier (-1) θ * g θ)) (g := fun θ => b₀ * g θ) (continuous_const.mul (hu (-1))) (continuous_const.mul hg)]
  simp only [fourierCoeff.const_mul, coeff_shift, sub_neg_eq_add]

variable {n : ℕ}

private theorem entry_cont {U : Field n} (hu : SmoothToBoundary U) {z : ℂ} (hz : z ∈ closedBall 0 1)
    (i j : Fin n) : Continuous (fun θ : Angle => U z θ.toCircle i j) := by
  apply continuous_coinduced_dom.mpr
  change Continuous (fun t : ℝ => U z (AddCircle.toCircle (t : Angle)) i j)
  simpa only [toCircle_angle] using (slice_smooth hu hz i j).continuous

private theorem entry_conv {B U : Field n} (hb : SmoothToBoundary B) (hu : SmoothToBoundary U)
    (hm : ThreeModes B) (z : ℂ) (hz : z ∈ closedBall 0 1) (i j p q : Fin n) (k : ℤ) :
    fourierCoeff (fun θ : Angle => B z θ.toCircle i j * U z θ.toCircle p q) k =
      modeMatrix B z (-1) i j * modeMatrix U z (k+1) p q +
      modeMatrix B z 0 i j * modeMatrix U z k p q +
      modeMatrix B z 1 i j * modeMatrix U z (k-1) p q := by
  have he (θ : Angle) := congrArg (fun M : Mat n => M i j) (threeMode_expansion hb hm z hz θ.toCircle)
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at he
  simp_rw [he]
  exact poly_times _ _ _ _ (entry_cont hu hz p q) k

/-- Coefficient convolution for left multiplication by a three-mode
attenuation, retaining matrix order. -/
theorem mode_left_mul {B U : Field n} (hb : SmoothToBoundary B) (hu : SmoothToBoundary U)
    (hm : ThreeModes B) (z : ℂ) (hz : z ∈ closedBall 0 1) (k : ℤ) :
    modeMatrix (B * U) z k = modeMatrix B z (-1) * modeMatrix U z (k+1) +
      modeMatrix B z 0 * modeMatrix U z k + modeMatrix B z 1 * modeMatrix U z (k-1) := by
  ext i j
  change fourierCoeff (fun θ : Angle => ∑ l, B z θ.toCircle i l * U z θ.toCircle l j) k = _
  rw [coeff_sum Finset.univ (fun l (θ : Angle) => B z θ.toCircle i l * U z θ.toCircle l j)
      (fun l => (entry_cont hb hz i l).mul (entry_cont hu hz l j))]
  simp only [entry_conv hb hu hm z hz, Finset.sum_add_distrib, Matrix.add_apply, Matrix.mul_apply]

/-- Coefficient convolution for the opposite multiplication order. -/
theorem mode_right_mul {B U : Field n} (hb : SmoothToBoundary B) (hu : SmoothToBoundary U)
    (hm : ThreeModes B) (z : ℂ) (hz : z ∈ closedBall 0 1) (k : ℤ) :
    modeMatrix (U * B) z k = modeMatrix U z (k+1) * modeMatrix B z (-1) +
      modeMatrix U z k * modeMatrix B z 0 + modeMatrix U z (k-1) * modeMatrix B z 1 := by
  ext i j
  change fourierCoeff (fun θ : Angle => ∑ l, U z θ.toCircle i l * B z θ.toCircle l j) k = _
  rw [coeff_sum Finset.univ (fun l (θ : Angle) => U z θ.toCircle i l * B z θ.toCircle l j)
      (fun l => (entry_cont hu hz i l).mul (entry_cont hb hz l j))]
  have he l : fourierCoeff (fun θ : Angle => U z θ.toCircle i l * B z θ.toCircle l j) k =
      modeMatrix U z (k+1) i l * modeMatrix B z (-1) l j +
      modeMatrix U z k i l * modeMatrix B z 0 l j + modeMatrix U z (k-1) i l * modeMatrix B z 1 l j := by
    simpa only [mul_comm] using entry_conv hb hu hm z hz l j i l k
  simp only [he, Finset.sum_add_distrib, Matrix.add_apply, Matrix.mul_apply]

private abbrev period := 2 * Real.pi

/-- The real base derivative passes through each normalized Haar coefficient.
Ambient differentiability at the specified base point and along the full
fiber is sufficient, even on the boundary of the base disk. -/
theorem derivative_mode (u : ℂ → Circle → ℂ) (z : ℂ) (k : ℤ)
    (hs : ∀ t : ℝ, ContDiffAt ℝ 1 (fun p : ℂ × ℝ => u p.1 (Circle.exp p.2)) (z,t)) :
    DifferentiableAt ℝ (fun p => fourierCoeff (fun θ : Angle => u p θ.toCircle) k) z ∧
    ∀ d : ℂ, fderiv ℝ (fun p => fourierCoeff (fun θ : Angle => u p θ.toCircle) k) z d =
      fourierCoeff (fun θ : Angle => fderiv ℝ (fun p => u p θ.toCircle) z d) k := by
  let g := fun p : ℂ × ℝ => fourier (-k) (p.2 : Angle) * u p.1 (Circle.exp p.2)
  have hg (t : ℝ) : ContDiffAt ℝ 1 g (z,t) := by
    apply ContDiffAt.mul _ (hs t)
    simp only [fourier_coe_apply]
    have hcoord : ContDiffAt ℝ 1 (fun x : ℂ × ℝ => (x.2 : ℂ)) (z,t) :=
      ofRealCLM.contDiff.contDiffAt.comp _ contDiffAt_snd
    fun_prop
  obtain ⟨H, Hint⟩ := CoefficientIntegral.interval_derivative g z two_pi_pos (fun t _ => hg t)
  let c : ℝ := 1 / period
  have he : (fun p => fourierCoeff (fun θ : Angle => u p θ.toCircle) k) =
      fun p => c • ∫ t in (0 : ℝ)..period, g (p,t) := by
    funext p
    rw [fourierCoeff_eq_intervalIntegral _ _ 0, zero_add]
    simp only [c, period, g, smul_eq_mul, toCircle_angle]
  rw [he]
  have ht := H.const_smul c
  simp only [Pi.smul_def] at ht
  refine ⟨ht.differentiableAt, ?_⟩
  intro d
  rw [ht.fderiv, ContinuousLinearMap.smul_apply, ContinuousLinearMap.intervalIntegral_apply Hint,
    fourierCoeff_eq_intervalIntegral _ _ 0, zero_add]
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  have hbase : DifferentiableAt ℝ (fun p => u p (Circle.exp t)) z :=
    (CoefficientIntegral.slice_hasFDeriv (hs t)).differentiableAt
  simp only [g, toCircle_angle, fderiv_const_mul hbase, ContinuousLinearMap.smul_apply, smul_eq_mul]

private theorem vertical_at_angle (u : ℂ → Circle → ℂ) (z : ℂ) (t : ℝ) :
    Isothermal.vertical u z (Circle.exp t) = deriv (fun s : ℝ => u z (Circle.exp s)) t := by
  simp only [Isothermal.vertical, ← Circle.exp_add]
  simpa only [add_zero] using deriv_comp_const_add (fun s : ℝ => u z (Circle.exp s)) t 0

/-- Integration by parts gives the multiplier ik for vertical
differentiation, with zero mean also included. -/
theorem mode_vertical (u : ℂ → Circle → ℂ) (z : ℂ) (k : ℤ)
    (hs : ContDiff ℝ 2 (fun t : ℝ => u z (Circle.exp t))) :
    fourierCoeff (fun θ : Angle => Isothermal.vertical u z θ.toCircle) k =
      I * (k : ℂ) * fourierCoeff (fun θ : Angle => u z θ.toCircle) k := by
  let g := fun t : ℝ => u z (Circle.exp t)
  have hp : g.Periodic period := fun t => congrArg (u z) (Circle.periodic_exp t)
  have sub (f : Angle → ℂ) : fourierCoeff f k = fourierCoeffOn Real.two_pi_pos (fun t : ℝ => f t) k := by
    rw [fourierCoeffOn_eq_integral, fourierCoeff_eq_intervalIntegral _ _ 0]
    simp
  rw [sub, sub (fun θ : Angle => u z θ.toCircle)]
  simp only [toCircle_angle, vertical_at_angle]
  change fourierCoeffOn Real.two_pi_pos (deriv g) k = I * (k:ℂ) * fourierCoeffOn Real.two_pi_pos g k
  have hdiff : Differentiable ℝ g := hs.differentiable (by decide)
  have h1 : ContDiff ℝ 1 (deriv g) := hs.deriv'
  have hcont : Continuous (deriv g) := h1.continuous
  by_cases hk : k = 0
  · subst k
    rw [fourierCoeffOn_eq_integral]
    simp only [Int.cast_zero, neg_zero, fourier_zero, one_smul, mul_zero, zero_mul]
    rw [intervalIntegral.integral_deriv_eq_sub (fun t _ => hdiff t) (hcont.intervalIntegrable _ _)]
    simp only [show g (2*π) = g 0 by simpa using hp 0, sub_self, smul_zero]
  · exact FourierDecay.derivative_coefficient g hp hdiff hcont k hk

private def slope (u : ℂ → Circle → ℂ) (z d : ℂ) (θ : Angle) : ℂ :=
  fderiv ℝ (fun p => u p θ.toCircle) z d

private def angular (u : ℂ → Circle → ℂ) (z : ℂ) (θ : Angle) : ℂ :=
  Isothermal.vertical u z θ.toCircle

/-- Raising uses sign +1, lowering sign −1. -/
def driftWeight (lam : ℂ → ℝ) (z sign : ℂ) : ℂ :=
  (fderiv ℝ lam z I : ℂ) / 2 - sign * (fderiv ℝ lam z 1 : ℂ) / (2*I)

private def part (lam : ℂ → ℝ) (u : ℂ → Circle → ℂ) (z sign : ℂ) (θ : Angle) : ℂ :=
  (1/2 : ℂ) * slope u z 1 θ + (sign/(2*I)) * slope u z I θ +
  driftWeight lam z sign * angular u z θ

private theorem continuous_slope (u : ℂ → Circle → ℂ) (z d : ℂ)
    (hs : ∀ t : ℝ, ContDiffAt ℝ 1 (fun p : ℂ × ℝ => u p.1 (Circle.exp p.2)) (z,t)) :
    Continuous (slope u z d) := by
  apply continuous_coinduced_dom.mpr
  change Continuous (fun t : ℝ => fderiv ℝ (fun p => u p (AddCircle.toCircle (t : Angle))) z d)
  simp only [toCircle_angle]
  let g := fun p : ℂ × ℝ => u p.1 (Circle.exp p.2)
  have h (t : ℝ) : fderiv ℝ (fun p => u p (Circle.exp t)) z =
      CoefficientIntegral.baseDerivative g (z,t) := (CoefficientIntegral.slice_hasFDeriv (hs t)).fderiv
  simp_rw [h]
  apply continuous_iff_continuousAt.mpr
  intro t
  exact (((CoefficientIntegral.baseDerivative_cont (hs t)).clm_apply continuousAt_const).comp
      (continuousAt_const.prodMk continuousAt_id))

private theorem continuous_angular (u : ℂ → Circle → ℂ) (z : ℂ)
    (hs : ContDiff ℝ 2 (fun t : ℝ => u z (Circle.exp t))) : Continuous (angular u z) := by
  apply continuous_coinduced_dom.mpr
  change Continuous (fun t : ℝ => Isothermal.vertical u z (AddCircle.toCircle (t : Angle)))
  simp only [toCircle_angle, vertical_at_angle]
  have h : ContDiff ℝ 1 (deriv (fun t : ℝ => u z (Circle.exp t))) := hs.deriv'
  exact h.continuous

private theorem continuous_part (lam : ℂ → ℝ) (u : ℂ → Circle → ℂ) (z sign : ℂ)
    (hs : ∀ t : ℝ, ContDiffAt ℝ 1 (fun p : ℂ × ℝ => u p.1 (Circle.exp p.2)) (z,t))
    (hu : ContDiff ℝ 2 (fun t : ℝ => u z (Circle.exp t))) : Continuous (part lam u z sign) :=
  ((continuous_const.mul (continuous_slope u z 1 hs)).add
    (continuous_const.mul (continuous_slope u z I hs))).add
    (continuous_const.mul (continuous_angular u z hu))

/-- Scalar angular coefficient, as a base function. -/
def coefficient (u : ℂ → Circle → ℂ) (k : ℤ) (z : ℂ) : ℂ :=
  fourierCoeff (fun θ : Angle => u z θ.toCircle) k

/-- Coefficient of the part of X changing a single input frequency in the
indicated direction, prior to the common factor exp(−λ). -/
def neighbor (lam : ℂ → ℝ) (u : ℂ → Circle → ℂ) (z sign : ℂ) (l : ℤ) : ℂ :=
  (1/2 : ℂ) * fderiv ℝ (coefficient u l) z 1 +
    (sign / (2*I)) * fderiv ℝ (coefficient u l) z I +
    driftWeight lam z sign * (I * (l:ℂ) * coefficient u l z)

private theorem coefficient_part (lam : ℂ → ℝ) (u : ℂ → Circle → ℂ) (z sign : ℂ) (l : ℤ)
    (hs : ∀ t : ℝ, ContDiffAt ℝ 1 (fun p : ℂ × ℝ => u p.1 (Circle.exp p.2)) (z,t))
    (hu : ContDiff ℝ 2 (fun t : ℝ => u z (Circle.exp t))) :
    fourierCoeff (part lam u z sign) l = neighbor lam u z sign l := by
  unfold part
  rw [coeff_add (f := fun θ => 1/2 * slope u z 1 θ + sign/(2*I) * slope u z I θ)
    (g := fun θ => driftWeight lam z sign * angular u z θ)
    ((continuous_const.mul (continuous_slope u z 1 hs)).add (continuous_const.mul (continuous_slope u z I hs)))
    (continuous_const.mul (continuous_angular u z hu))]
  rw [coeff_add (f := fun θ => 1/2 * slope u z 1 θ) (g := fun θ => sign/(2*I) * slope u z I θ)
    (continuous_const.mul (continuous_slope u z 1 hs)) (continuous_const.mul (continuous_slope u z I hs))]
  simp only [fourierCoeff.const_mul, slope, angular, mode_vertical u z l hu,
    ← (derivative_mode u z l hs).2, neighbor, coefficient]
  rfl

/-- The geodesic vector field on unrestricted smooth profiles couples only
the two adjacent Haar modes. This includes the angular drift from λ. -/
theorem coefficient_geodesicX (lam : ℂ → ℝ) (u : ℂ → Circle → ℂ) (z : ℂ) (k : ℤ)
    (hs : ∀ t : ℝ, ContDiffAt ℝ 1 (fun p : ℂ × ℝ => u p.1 (Circle.exp p.2)) (z,t))
    (hu : ContDiff ℝ 2 (fun t : ℝ => u z (Circle.exp t))) :
    coefficient (Isothermal.geodesicX lam u) k z = (Real.exp (-lam z) : ℂ) *
      (neighbor lam u z 1 (k-1) + neighbor lam u z (-1) (k+1)) := by
  have he : (fun θ : Angle => Isothermal.geodesicX lam u z θ.toCircle) = fun θ =>
      (Real.exp (-lam z) : ℂ) * (fourier 1 θ * part lam u z 1 θ + fourier (-1) θ * part lam u z (-1) θ) := by
    funext θ
    rw [Isothermal.geodesicX, Fourier.flatX, Fourier.linear_split _ θ.toCircle, fourier_neg (n := 1), fourier_one]
    simp only [part, slope, angular, driftWeight, Isothermal.angularDrift,
      Complex.ofReal_sub, Complex.ofReal_mul]
    rw [Complex.re_eq_add_conj, Complex.im_eq_sub_conj, ← Circle.coe_inv_eq_conj, Circle.coe_inv]
    ring
  unfold coefficient
  rw [he, fourierCoeff.const_mul, coeff_add (f := fun θ => fourier 1 θ * part lam u z 1 θ)
    (g := fun θ => fourier (-1) θ * part lam u z (-1) θ)
    ((fourier 1).continuous.mul (continuous_part lam u z 1 hs hu))
    ((fourier (-1)).continuous.mul (continuous_part lam u z (-1) hs hu))]
  simp only [coeff_shift, sub_neg_eq_add, coefficient_part lam u z _ _ hs hu]

/-- For smooth matrix fields on the closed disk, the lower Fourier bound is
lowered by at most one, at all base points including the boundary. -/
theorem chartX_modes {U : Field n} (lam : ℂ → ℝ) (hs : SmoothToBoundary U) {m : ℤ}
    (hm : ModesFrom m U) : ModesFrom (m-1) (chartX lam U) := by
  intro z hz i j k hk
  let u := fun p v => U p v i j
  have hC (t : ℝ) : ContDiffAt ℝ 1 (fun p : ℂ × ℝ => u p.1 (Circle.exp p.2)) (z,t) :=
    (hs z hz t i j).of_le (by decide)
  have hu : ContDiff ℝ 2 (fun t : ℝ => u z (Circle.exp t)) := (slice_smooth hs hz i j).of_le (by decide)
  change coefficient (Isothermal.geodesicX lam u) k z = 0
  rw [coefficient_geodesicX lam u z k hC hu]
  have vanish (sign : ℂ) (l : ℤ) (hl : l < m) : neighbor lam u z sign l = 0 := by
    have h0 : Set.EqOn (coefficient u l) (fun _ => 0) (closedBall (0:ℂ) 1) := fun p hp => hm p hp i j l hl
    have huniq : UniqueDiffWithinAt ℝ (closedBall (0:ℂ) 1) z :=
      uniqueDiffOn_convex (convex_closedBall _ _) ⟨0, by
        rw [interior_closedBall _ (by norm_num : (1:ℝ) ≠ 0)]
        exact mem_ball_self (by norm_num)⟩ z hz
    have hd : fderiv ℝ (coefficient u l) z = 0 := by
      have ha : DifferentiableAt ℝ (coefficient u l) z := (derivative_mode u z l hC).1
      rw [← ha.fderivWithin huniq, fderivWithin_congr h0 (h0 hz)]
      simp
    simp [neighbor, h0 hz, hd]
  rw [vanish 1 (k-1) (by omega), vanish (-1) (k+1) (by omega), add_zero, mul_zero]

end TransportOkaGrauert.ChartCoefficients
