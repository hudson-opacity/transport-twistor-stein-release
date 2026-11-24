import TransportOkaGrauert.ChartModes
/-! A single positive shift reduces the lower angular cutoff −1 to the
holomorphic cutoff. This applies to arbitrary smooth angular series. -/
noncomputable section
namespace TransportOkaGrauert.ShiftedModes
open SimpleDiskTarget ChartModes Metric
open scoped ContDiff
local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩
variable {n : ℕ}

def shift (F : Field n) : Field n := fun z v => (v : ℂ) • F z v

theorem smooth_shift {F : Field n} (h : SmoothToBoundary F) : SmoothToBoundary (shift F) := by
  have hw : ContDiff ℝ ∞ (fun t : ℝ => (Circle.exp t : ℂ)) := by
    convert contDiff_circleMap 0 1 using 1
    funext t
    simp [circleMap, Circle.coe_exp]
  intro z hz θ i j
  exact (hw.comp contDiff_snd).contDiffAt.mul (h z hz θ i j)

theorem coeff_shift (f : DiskSeries.Angle → ℂ) (k : ℤ) :
    fourierCoeff (fun θ => (θ.toCircle : ℂ) * f θ) k = fourierCoeff f (k-1) := by
  have hv (θ : DiskSeries.Angle) : fourier (-(k-1)) θ = fourier (-k) θ * (θ.toCircle : ℂ) := by
    rw [show -(k-1) = -k + 1 by omega, fourier_add, fourier_one]
  simp only [fourierCoeff, hv, smul_eq_mul, mul_assoc]

theorem shifted_iff (F : Field n) : ModesFrom 0 (shift F) ↔ ModesFrom (-1) F := by
  constructor
  · intro h z hz i j k hk
    have hh := h z hz i j (k+1) (by omega)
    change fourierCoeff (fun θ => (θ.toCircle : ℂ) * F z θ.toCircle i j) (k+1) = 0 at hh
    simpa only [coeff_shift, add_sub_cancel_right] using hh
  · intro h z hz i j k hk
    change fourierCoeff (fun θ => (θ.toCircle : ℂ) * F z θ.toCircle i j) k = 0
    exact (coeff_shift _ _).trans (h z hz i j _ (by omega))

theorem mul_right {A G : Field n} (ha : SmoothToBoundary A) (hg : SmoothToBoundary G)
    (ma : ModesFrom (-1) A) (mg : ModesFrom 0 G) : ModesFrom (-1) (A*G) := by
  apply (shifted_iff _).mp
  convert modes_mul (smooth_shift ha) hg ((shifted_iff _).mpr ma) mg using 1
  funext z v
  exact (smul_mul_assoc _ _ _).symm

theorem mul_left {G A : Field n} (hg : SmoothToBoundary G) (ha : SmoothToBoundary A)
    (mg : ModesFrom 0 G) (ma : ModesFrom (-1) A) : ModesFrom (-1) (G*A) := by
  apply (shifted_iff _).mp
  convert modes_mul hg (smooth_shift ha) mg ((shifted_iff _).mpr ma) using 1
  funext z v
  exact (mul_smul_comm _ _ _).symm

end TransportOkaGrauert.ShiftedModes
