import TransportOkaGrauert.ScalarWKernelBridge
import TransportOkaGrauert.ScalarNormalLift

/-! # Localizing a common smooth ray kernel on the disk -/
noncomputable section
namespace TransportOkaGrauert.ScalarWRangeBridge
open Complex Set Metric MeasureTheory
open SimpleDiskTarget JacobiEnlargement GeodesicFlowExtension ScalarRayPairing ScalarNormalLift ScalarWPrimitive
open scoped ContDiff Topology

/-- A single smooth spatial kernel on the compact product containing the
cutoff support suffices for local surjectivity. The left cutoff absorbs
all centres outside the product, including those near the disk boundary. -/
theorem localize_kernel {σ : ℂ → ℝ} (simple : SimpleMetric σ) {r : ℝ} (hr : 0 < r) (hr₁ : r < 1)
    (kernel : ∀ (B : Set ℂ), IsCompact B → B ⊆ ball (0:ℂ) 1 →
      ∃ k : ℂ × ℂ → ℝ, ContDiff ℝ ∞ k ∧ ∀ (F : Flow σ) (T : ℝ), 0 < T → Escapes F T →
        ∀ g : ℂ → ℝ, ContDiff ℝ ∞ g → (∀ z ∉ B, g z = 0) →
          ∀ z ∈ B, Wvalue σ F T g z = ∫ y in ball (0:ℂ) 1, k (z,y)*g y) : HasParametrix σ r := by
  let R := (r+1)/2
  have less : r < R := by dsimp [R]; linarith
  have inside : R < 1 := by dsimp [R]; linarith
  let B := closedBall (0:ℂ) R
  let χ : ContDiffBump (0:ℂ) := ⟨r,R,hr,less⟩
  have off (z : ℂ) (hz : z ∉ B) : χ z = 0 := by
    apply χ.zero_of_le_dist
    exact le_of_not_ge (fun h => hz (mem_closedBall.mpr h))
  have outside (z : ℂ) (hz : 1 < ‖z‖) : χ z = 0 := by
    apply off
    exact fun h => (not_le_of_gt (inside.trans hz)) (mem_closedBall_zero_iff.mp h)
  have one (z : ℂ) (hz : z ∈ ball (0:ℂ) r) : χ z = 1 :=
    χ.one_of_mem_closedBall (ball_subset_closedBall hz)
  obtain ⟨k,sk,act⟩ := kernel B (isCompact_closedBall _ _) (closedBall_subset_ball inside)
  obtain ⟨F⟩ := JacobiEnlargement.exists_flow simple
  obtain ⟨T,ht,esc⟩ := ScalarNormalLift.exists_time simple F
  let W : Window F := ⟨T,ht,fun p hp => (esc p hp).1⟩
  let full (p : ℂ × ℂ) := χ p.1 * k p * χ p.2
  have sfull : ContDiff ℝ ∞ full := ((χ.contDiff.comp contDiff_fst).mul sk).mul (χ.contDiff.comp contDiff_snd)
  apply of_kernel simple F W hr₁.le χ χ.contDiff outside one full sfull
  intro f sf z _
  let g := fun y => χ y*f y
  have sg : ContDiff ℝ ∞ g := χ.contDiff.mul sf
  have goff : ∀ y ∉ B, g y = 0 := fun y hy => by simp [g,off y hy]
  have regroup (y : ℂ) : full (z,y)*f y = χ z * (k (z,y)*g y) := by
    dsimp [full,g]; ring
  simp_rw [regroup]
  rw [integral_const_mul]
  by_cases hz : z ∈ B
  · exact congrArg (fun t => χ z*t) (act F T ht esc g sg goff z hz)
  · simp [cut,off z hz]
end TransportOkaGrauert.ScalarWRangeBridge
