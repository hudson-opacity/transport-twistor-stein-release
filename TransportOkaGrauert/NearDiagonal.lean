import TransportOkaGrauert.MixedCorrection
import TransportOkaGrauert.ChartOrbits

/-! Global frames from a local, zeroth-order estimate for a linear mixed
transport equation. The correction need not depend continuously on either
parameter. Its base and fibre regularity remains essential. -/
noncomputable section
namespace TransportOkaGrauert.NearDiagonal
open SimpleDiskTarget ChartOrbits MixedCorrection Metric Set
open scoped Matrix.Norms.Operator
variable {n : ℕ}
abbrev Interval := Set.Icc (0 : ℝ) 1

/-- At each base amplitude t, demand only bounded smooth solutions for one
fixed forcing term −A at nearby distinct amplitudes. No estimate for general
right-hand sides or for derivatives of the selected solutions is used below. -/
def BoundedMixedSolvability (lam : ℂ → ℝ) (A : Field n) : Prop :=
  ∀ t : Interval, ∃ C ε : ℝ, 0 ≤ C ∧ 0 < ε ∧
    ∀ s : Interval, s ≠ t → |(t:ℝ) - s| < ε →
    ∃ U : Field n, SmoothToBoundary U ∧ ModesFrom 0 U ∧ Solves lam A U t s ∧
      ∀ z ∈ closedBall (0:ℂ) 1, ∀ v : Circle, ‖U z v‖ ≤ C

theorem relative_step {lam : ℂ → ℝ} {A U : Field n} {t s C : ℝ}
    (hu : SmoothToBoundary U) (hm : ModesFrom 0 U) (h : Solves lam A U t s)
    (bound : ∀ z ∈ closedBall (0:ℂ) 1, ∀ v : Circle, ‖U z v‖ ≤ C)
    (small : |t-s| * C < 1) :
    ∃ F G, RelativeFrame lam (t • A) (s • A) F G := by
  have hb (z : ℂ) (hz : z ∈ closedBall 0 1) (v : Circle) :
      ‖((t-s) • U) z v‖ ≤ |t-s| * C := by
    change ‖(t-s) • U z v‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (bound z hz v) (abs_nonneg _)
  obtain ⟨G, hf, hg, mf, mg, inv⟩ := NearIdentity.small_gauge ((t-s) • U)
    (scaled_smooth hu _) (scaled_modes hm _) small hb
  exact ⟨step U (t-s), G, hf, hg, mf, mg, inv, intertwines h⟩

/-- Conditional general rank theorem on the actual metric chart. -/
theorem frame_of_bounded_mixed_solutions {lam : ℂ → ℝ} {A : Field n}
    (linear : BoundedMixedSolvability lam A) : ∃ F G, IsFrame lam A F G := by
  apply frame_of_local_along_ray
  intro t
  obtain ⟨C, ε, hC, hε, solve⟩ := linear t
  have hpos : 0 < C+1 := by linarith
  let δ := min ε (1 / (C+1))
  have hd : 0 < δ := lt_min hε (one_div_pos.mpr hpos)
  refine ⟨ball t δ, isOpen_ball, mem_ball_self hd, ?_⟩
  intro s hs
  by_cases he : s = t
  · subst s
    exact ⟨1, 1, RelativeFrame.refl _ _⟩
  have hdist : |(t:ℝ) - s| < δ := by
    change dist s t < δ at hs
    simpa only [Subtype.dist_eq, Real.dist_eq, abs_sub_comm (s:ℝ) t] using hs
  obtain ⟨U, hu, hm, h, hb⟩ := solve s he (hdist.trans_le (min_le_left _ _))
  apply relative_step hu hm h hb
  have hmul := (lt_div_iff₀ hpos).mp (hdist.trans_le (min_le_right _ _))
  nlinarith [abs_nonneg ((t:ℝ) - s)]

/-- The universal simple-disk target follows from the mixed linear estimate.
Simplicity enters through the construction and bounds for its solutions. -/
theorem chartTarget_of_bounded_mixed
    (estimate : ∀ (lam : ℂ → ℝ), SimpleMetric lam → ∀ (n : ℕ) (A : Field n),
      SmoothToBoundary A → ModesFrom (-1) A → BoundedMixedSolvability lam A) :
    chartIntegratingFactorTarget := by
  intro lam hl n A ha hm
  exact frame_of_bounded_mixed_solutions (estimate lam hl n A ha hm)

end TransportOkaGrauert.NearDiagonal
