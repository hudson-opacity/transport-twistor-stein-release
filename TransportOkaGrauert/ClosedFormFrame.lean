import TransportOkaGrauert.ClosedForm
import TransportOkaGrauert.ModeCalibration
import TransportOkaGrauert.BoundaryModes

/-! A curved-chart instance at the exact frame type used in the general target. -/
namespace TransportOkaGrauert.ClosedForm
noncomputable section
open SimpleDiskTarget Metric
open scoped ContDiff
local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

def asMatrix (F : ℂ → Circle → ℂ) : Field 1 := fun z w _ _ => F z w

private theorem smooth_base (s : Set ℂ) (ho : IsOpen s) (disk : closedBall 0 1 ⊆ s)
    {f : ℂ → ℂ} (h : ContDiffOn ℝ ∞ f s) : SmoothToBoundary (asMatrix (fun z _ => f z)) :=
  fun z hz t _ _ => (h.contDiffAt (ho.mem_nhds (disk hz))).comp (z,t) contDiffAt_fst

private theorem constant_modes (f : ℂ → ℂ) : ModesFrom 0 (asMatrix (fun z _ => f z)) := by
  intro z _ _ _ k hk
  exact BoundaryModes.negativeMode_eq_zero
    (f := fun _ : ℂ => f z) (differentiable_const _).diffContOnCl k hk

/-- A closed one-form on a convex open neighborhood of the disk gives an
admissible attenuation and a rank-one holomorphic frame for every smooth conformal metric. -/
theorem closedForm_chart_frame (lam : ℂ → ℝ) (metric_smooth : ContDiff ℝ ∞ lam)
    (s : Set ℂ) (hs : Convex ℝ s) (ho : IsOpen s) (disk : closedBall 0 1 ⊆ s)
    (form : ℂ → ℂ →L[ℝ] ℂ) (smooth : ContDiffOn ℝ ∞ form s)
    (closed : ∀ z ∈ s, ∀ v w, fderiv ℝ form z v w = fderiv ℝ form z w v) :
    let A := asMatrix (attenuation lam form)
    SmoothToBoundary A ∧ ModesFrom (-1) A ∧ ∃ F G, IsFrame lam A F G := by
  dsimp only
  obtain ⟨f,g,hf,hg,hinv,hx⟩ := integrating_factor lam s hs ho form smooth closed
  refine ⟨?_, ?_, asMatrix (fun z _ => f z), asMatrix (fun z _ => g z),
    smooth_base s ho disk hf, smooth_base s ho disk hg, constant_modes f, constant_modes g, ?_, ?_⟩
  · intro z hz t i j
    have hbase := (smooth.contDiffAt (ho.mem_nhds (disk hz))).comp (z,t) contDiffAt_fst
    have hvel : ContDiff ℝ ∞ (fun x : ℝ => (Circle.exp x : ℂ)) := by
      convert contDiff_circleMap 0 1 using 1
      funext x
      simp [circleMap, Circle.coe_exp]
    unfold asMatrix attenuation
    have hmetric : ContDiff ℝ ∞ (fun p : ℂ × ℝ => (Real.exp (-lam p.1) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (metric_smooth.comp contDiff_fst).neg.exp
    exact hmetric.contDiffAt.mul (hbase.clm_apply (hvel.comp contDiff_snd).contDiffAt)
  · intro z _ _ _ k hk
    exact ModeCalibration.linearForm_modes (form z) _ _ hk
  · intro z _ w
    constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      simpa [asMatrix, Matrix.mul_apply, mul_comm] using hinv z
  · intro z hz w i j
    simpa [asMatrix, Matrix.mul_apply] using hx z (disk hz) w

end
end TransportOkaGrauert.ClosedForm
