import TransportOkaGrauert.SimpleDiskTarget

/-!
# From finite character expansions to normalized Haar coefficients

This identifies the finite mode calculus with the Fourier convention in the
simple-disk target. In particular, real-linear forms of a unit velocity
have no frequencies less than −1.
-/

noncomputable section

namespace TransportOkaGrauert.ModeCalibration

open MeasureTheory Fourier SimpleDiskTarget Complex

local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

private abbrev Angle := AddCircle (2 * Real.pi)

private theorem character_on_angle (k : ℤ) (θ : Angle) :
    character k θ.toCircle = fourier k θ := by
  rw [fourier_apply, AddCircle.toCircle_zsmul, Circle.coe_zpow, character]

private theorem finiteModes_continuous {m : ℤ} {f : Circle → ℂ} (h : FiniteModes m f) :
    Continuous (fun θ : Angle => f θ.toCircle) := by
  induction h with
  | zero => exact continuous_const
  | mode k hk a =>
    simp only [character_on_angle]
    exact continuous_const.mul (fourier k).continuous
  | add _ _ hf hg => exact hf.add hg

/-- The finite character lower bound implies the corresponding vanishing
of actual normalized Haar Fourier coefficients on the angular circle. -/
theorem finiteModes_coefficient_zero {m k : ℤ} {f : Circle → ℂ}
    (h : FiniteModes m f) (hk : k < m) :
    fourierCoeff (fun θ : AddCircle (2 * Real.pi) => f θ.toCircle) k = 0 := by
  induction h with
  | zero => simp [fourierCoeff]
  | mode j hj a =>
    simp only [character_on_angle]
    rw [fourierCoeff.const_mul, fourierCoeff_fourier]
    simp [Pi.single_eq_of_ne (show k ≠ j by omega)]
  | @add f g hf hg ihf ihg =>
    change fourierCoeff ((fun θ : Angle => f θ.toCircle) + (fun θ => g θ.toCircle)) k = 0
    rw [fourierCoeff.add ((finiteModes_continuous hf).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)) ((finiteModes_continuous hg).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))]
    exact (congrArg₂ (· + ·) ihf ihg).trans (add_zero _)

/-- Entrywise finite expansions supply precisely the Fourier lower-bound
condition used for disk attenuations and gauges. -/
theorem modesFrom_of_finiteModes {n : ℕ} {m : ℤ} {F : Field n}
    (h : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, ∀ (i j : Fin n),
      FiniteModes m (fun w => F z w i j)) : ModesFrom m F :=
  fun z hz i j _ hk => finiteModes_coefficient_zero (h z hz i j) hk

/-- A real-linear form on the unit velocity has only the two characters
of frequencies +1 and −1. -/
theorem linearForm_finiteModes (L : ℂ →L[ℝ] ℂ) (c : ℂ) :
    FiniteModes (-1) (fun w : Circle => c * L (w : ℂ)) := by
  have h := (FiniteModes.mode 1 (show (-1 : ℤ) ≤ 1 by decide)
      (c * (L 1 / 2 + L I / (2 * I)))).add
    (FiniteModes.mode (-1) (le_refl (-1 : ℤ)) (c * (L 1 / 2 - L I / (2 * I))))
  convert h using 1
  funext w
  rw [Fourier.linear_split L w]
  simp only [Pi.add_apply, character, zpow_one, zpow_neg_one]
  ring

/-- Multiplying a real-linear form of the velocity by a fixed scalar
preserves the attenuation cutoff −1. -/
theorem linearForm_modes (L : ℂ →L[ℝ] ℂ) (c : ℂ) (k : ℤ) (hk : k < -1) :
    fourierCoeff (fun θ : AddCircle (2 * Real.pi) => c * L (θ.toCircle : ℂ)) k = 0 :=
  finiteModes_coefficient_zero (linearForm_finiteModes L c) hk

end TransportOkaGrauert.ModeCalibration
