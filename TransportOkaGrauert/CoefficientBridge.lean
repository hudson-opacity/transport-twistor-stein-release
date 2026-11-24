import TransportOkaGrauert.SkewReduction
import TransportOkaGrauert.PathContinuation

/-! Uniqueness of the normalized angular Fourier coefficients and its application
to the inhomogeneous mixed transport equation on the closed chart disk. -/

noncomputable section
namespace TransportOkaGrauert.CoefficientBridge

open SimpleDiskTarget SkewReduction MixedCorrection ChartModes PathContinuation
open Metric MeasureTheory
open scoped ContDiff

/-- A continuous function whose normalized Haar coefficients vanish is zero
at every point. Its zero coefficient sequence is automatically summable. -/
theorem eq_zero_of_coeff_zero {T : ℝ} [Fact (0 < T)] (f : C(AddCircle T, ℂ))
    (h : ∀ k : ℤ, fourierCoeff f k = 0) (θ : AddCircle T) : f θ = 0 := by
  have hsum : Summable (fourierCoeff f) := by simpa only [funext h] using
    (summable_zero : Summable (fun _ : ℤ => (0 : ℂ)))
  have hf := (has_pointwise_sum_fourier_series_of_summable hsum θ).tsum_eq
  simpa only [h, zero_smul, tsum_zero] using hf.symm

/-- Normalized Haar coefficients uniquely determine a continuous angular
function, even if the coefficients of the function itself are not summable. -/
theorem eq_of_coeff_eq {T : ℝ} [Fact (0 < T)] {f g : AddCircle T → ℂ}
    (hf : Continuous f) (hg : Continuous g) (h : ∀ k : ℤ, fourierCoeff f k = fourierCoeff g k) :
    f = g := by
  let d : C(AddCircle T, ℂ) := ⟨fun x => f x - g x, hf.sub hg⟩
  have hd (k : ℤ) : fourierCoeff d k = 0 := by
    have hi (v : AddCircle T → ℂ) (hv : Continuous v) :
        Integrable (fun x => fourier (-k) x • v x) AddCircle.haarAddCircle :=
      ((fourier (-k)).continuous.smul hv).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    simp only [d, ContinuousMap.coe_mk, fourierCoeff, smul_sub, integral_sub (hi f hf) (hi g hg)]
    exact sub_eq_zero.mpr (h k)
  funext θ
  exact sub_eq_zero.mp (eq_zero_of_coeff_zero d hd θ)

local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩
private abbrev Angle := DiskSeries.Angle

/-- At a fixed base point smoothness in the base and a frequency cutoff
are unnecessary. Entrywise angular continuity suffices. -/
theorem matrix_eq_of_modeMatrix_eq {ι : Type*} {F G : ℂ → Circle → Matrix ι ι ℂ} {z : ℂ}
    (hF : ∀ i j, Continuous (fun θ : Angle => F z θ.toCircle i j))
    (hG : ∀ i j, Continuous (fun θ : Angle => G z θ.toCircle i j))
    (h : ∀ k, modeMatrix F z k = modeMatrix G z k) (v : Circle) :
    F z v = G z v := by
  let θ : Angle := (Complex.arg (v : ℂ) : ℝ)
  have hv : θ.toCircle = v := (toCircle_angle _).trans (Circle.exp_arg v)
  ext i j
  have he := eq_of_coeff_eq (hF i j) (hG i j) (fun k =>
    congrArg (fun M : Matrix ι ι ℂ => M i j) (h k))
  simpa only [hv] using congrFun he θ

variable {n : ℕ}

/-- At fixed position the metric and its first derivatives are constants.
Only C¹ regularity of the unknown along the lifted fiber is needed for
angular continuity of the actual geodesic derivative. -/
theorem derivX_entry_continuous {lam : ℂ → ℝ} {U : Field n} {z : ℂ} {i j : Fin n}
    (h : ∀ t : ℝ, ContDiffAt ℝ 1 (fun p : ℂ × ℝ => U p.1 (Circle.exp p.2) i j) (z,t)) :
    Continuous (fun θ : Angle => derivX lam U z θ.toCircle i j) := by
  apply continuous_coinduced_dom.mpr
  change Continuous (fun t : ℝ => derivX lam U z (AddCircle.toCircle (t : Angle)) i j)
  simp only [toCircle_angle, derivX]
  rw [show (fun t : ℝ => Isothermal.geodesicX lam (fun p w => U p w i j) z (Circle.exp t)) =
      fun t : ℝ => fderiv ℝ (fun p : ℂ × ℝ => U p.1 (Circle.exp p.2) i j) (z,t)
        (chartVector lam (z,t)) from funext fun t =>
      geodesicX_eq_chart_derivative _ _ _ _ ((h t).differentiableAt (by decide))]
  apply continuous_iff_continuousAt.mpr
  intro t
  apply ContinuousAt.clm_apply ((h t).continuousAt_fderiv (by decide) |>.comp
    (continuousAt_const.prodMk continuousAt_id))
  simp only [chartVector, Isothermal.angularDrift]
  fun_prop

private theorem mixed_coeff (a b c : Angle → ℂ) (ha : Continuous a) (hb : Continuous b)
    (hc : Continuous c) (t s : ℝ) (k : ℤ) :
    fourierCoeff (fun θ => a θ + (t : ℂ) * b θ - (s : ℂ) * c θ) k =
      fourierCoeff a k + (t : ℂ) * fourierCoeff b k - (s : ℂ) * fourierCoeff c k := by
  have hi {w : Angle → ℂ} (hw : Continuous w) : Integrable w AddCircle.haarAddCircle :=
    hw.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have htw : Continuous (fun θ => (t : ℂ) * b θ) := continuous_const.mul hb
  have hsw : Continuous (fun θ => (-(s : ℂ)) * c θ) := continuous_const.mul hc
  have he : (fun θ => a θ + (t : ℂ) * b θ - (s : ℂ) * c θ) =
      (a + (fun θ => (t : ℂ) * b θ)) + (fun θ => (-(s : ℂ)) * c θ) := by
    funext θ
    simp [sub_eq_add_neg]
  rw [he, fourierCoeff.add (hi (ha.add htw)) (hi hsw),
    fourierCoeff.add (hi ha) (hi htw)]
  simp only [Pi.add_apply, fourierCoeff.const_mul]
  ring

/-- Solving the matrix PDE on the closed disk is equivalent to solving all
of its actual Haar coefficient equations. The two products retain their
orders. The conformal factor is arbitrary. -/
theorem solves_iff_coefficients_of_C1 {lam : ℂ → ℝ} {A U : Field n} (t s : ℝ)
    (ha : ∀ z ∈ closedBall (0 : ℂ) 1, ∀ i j : Fin n, Continuous (fun θ : Angle => A z θ.toCircle i j))
    (hu : ∀ z ∈ closedBall (0 : ℂ) 1, ∀ (θ : ℝ) (i j : Fin n),
      ContDiffAt ℝ 1 (fun p : ℂ × ℝ => U p.1 (Circle.exp p.2) i j) (z,θ)) :
    Solves lam A U t s ↔ ∀ z ∈ closedBall (0 : ℂ) 1, ∀ k : ℤ,
      modeMatrix (derivX lam U) z k + t • modeMatrix (A * U) z k -
        s • modeMatrix (U * A) z k = -modeMatrix A z k := by
  let lhs : Field n := fun z v => derivX lam U z v + t • (A * U) z v - s • (U * A) z v
  have hX (z : ℂ) (hz : z ∈ closedBall 0 1) (i j : Fin n) :=
    derivX_entry_continuous (lam := lam) (fun θ => hu z hz θ i j)
  have hU (z : ℂ) (hz : z ∈ closedBall 0 1) (i j : Fin n) :
      Continuous (fun θ : Angle => U z θ.toCircle i j) := by
    apply continuous_coinduced_dom.mpr
    change Continuous (fun t : ℝ => U z (AddCircle.toCircle (t : Angle)) i j)
    simp only [toCircle_angle]
    exact continuous_iff_continuousAt.mpr fun t =>
      (hu z hz t i j).continuousAt.comp (continuousAt_const.prodMk continuousAt_id)
  have hmul (F G : Field n) (z : ℂ)
      (hF : ∀ i j, Continuous (fun θ : Angle => F z θ.toCircle i j))
      (hG : ∀ i j, Continuous (fun θ : Angle => G z θ.toCircle i j)) (i j : Fin n) :
      Continuous (fun θ : Angle => (F * G) z θ.toCircle i j) :=
    continuous_finset_sum Finset.univ fun l _ => (hF i l).mul (hG l j)
  have hAU (z : ℂ) (hz : z ∈ closedBall 0 1) := hmul A U z (ha z hz) (hU z hz)
  have hUA (z : ℂ) (hz : z ∈ closedBall 0 1) := hmul U A z (hU z hz) (ha z hz)
  have hL (z : ℂ) (hz : z ∈ closedBall 0 1) (i j : Fin n) :
      Continuous (fun θ : Angle => lhs z θ.toCircle i j) :=
    ((hX z hz i j).add ((hAU z hz i j).const_smul t)).sub
      ((hUA z hz i j).const_smul s)
  have hR (z : ℂ) (hz : z ∈ closedBall 0 1) (i j : Fin n) :
      Continuous (fun θ : Angle => (-A) z θ.toCircle i j) := (ha z hz i j).neg
  have hleft (z : ℂ) (hz : z ∈ closedBall 0 1) (k : ℤ) : modeMatrix lhs z k =
      modeMatrix (derivX lam U) z k + t • modeMatrix (A*U) z k - s • modeMatrix (U*A) z k := by
    ext i j
    exact mixed_coeff _ _ _ (hX z hz i j) (hAU z hz i j) (hUA z hz i j) t s k
  have hright (z : ℂ) (k : ℤ) : modeMatrix (-A) z k = - modeMatrix A z k := by
    ext i j
    simp [modeMatrix, fourierCoeff, integral_neg]
  have hl (z : ℂ) (v : Circle) : lhs z v =
      derivX lam U z v + (t • A z v) * U z v - U z v * (s • A z v) := by
    simp only [lhs, Pi.mul_apply, smul_mul_assoc, mul_smul_comm]
  constructor
  · intro h z hz k
    rw [← hleft z hz, ← hright]
    ext i j
    apply congrArg (fun w : Angle → ℂ => fourierCoeff w k)
    funext θ
    exact congrArg (fun M : Mat n => M i j) ((hl z θ.toCircle).trans (h z hz θ.toCircle))
  · intro h z hz v
    rw [← hl]
    exact matrix_eq_of_modeMatrix_eq (hL z hz) (hR z hz)
      (fun k => (hleft z hz k).trans ((h z hz k).trans (hright z k).symm)) v

/-- The coefficient characterization under the chart target's regularity assumptions. -/
theorem solves_iff_coefficients {lam : ℂ → ℝ} {A U : Field n} (t s : ℝ)
    (ha : SmoothToBoundary A) (hu : SmoothToBoundary U) :
    Solves lam A U t s ↔ ∀ z ∈ closedBall (0 : ℂ) 1, ∀ k : ℤ,
      modeMatrix (derivX lam U) z k + t • modeMatrix (A * U) z k -
        s • modeMatrix (U * A) z k = -modeMatrix A z k :=
  solves_iff_coefficients_of_C1 t s (entry_continuous ha)
    (fun z hz θ i j => (hu z hz θ i j).of_le (by decide))

end TransportOkaGrauert.CoefficientBridge
