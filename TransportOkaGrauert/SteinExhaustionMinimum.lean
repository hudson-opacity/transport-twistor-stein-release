import TransportOkaGrauert.PhysicalSteinStrict
import TransportOkaGrauert.SteinTwistorCoordinates

/-! # Normalization of the physical strict exhaustion

Compact sublevels and smoothness give an attained global minimum and hence
the lower bound in the usual statement of the Levi criterion. -/
namespace TransportOkaGrauert.PhysicalStein
open ChartStein FrameLevi Set Metric
open scoped ContDiff

theorem bounded_below_exhaustion {σ : ℂ → ℝ} (s : SimpleDiskTarget.SimpleMetric σ) :
    ∃ f : E → ℝ, (∃ b : ℝ, ∀ p ∈ ChartSteinAtlas.domain (ball 0 1), b ≤ f p) ∧
      (∀ p ∈ ChartSteinAtlas.domain (ball 0 1), ContDiffAt ℝ ∞ f p ∧
        ∀ v : E, v ≠ 0 → 0 < ddC (J σ) f p v (J σ p v)) ∧
      ∀ t : ℝ, IsCompact {p ∈ ChartSteinAtlas.domain (ball (0:ℂ) 1) | f p ≤ t} := by
  obtain ⟨f,strict,proper⟩ := full_disk_levi_exhaustion s
  let D := ChartSteinAtlas.domain (ball (0:ℂ) 1)
  have zeroD : (0:E) ∈ D := by simp [D,ChartSteinAtlas.domain]
  let C := {p ∈ D | f p ≤ f 0}
  have nonempty : C.Nonempty := ⟨0,zeroD,le_rfl⟩
  have cont : ContinuousOn f C := fun p hp => (strict p hp.1).1.continuousAt.continuousWithinAt
  obtain ⟨a,ac,min⟩ := (proper (f 0)).exists_isMinOn nonempty cont
  refine ⟨f,⟨f a,?_⟩,strict,proper⟩
  intro p hp
  by_cases h : f p ≤ f 0
  · exact isMinOn_iff.mp min p ⟨hp,h⟩
  · exact ac.2.trans (le_of_lt (lt_of_not_ge h))
end TransportOkaGrauert.PhysicalStein
