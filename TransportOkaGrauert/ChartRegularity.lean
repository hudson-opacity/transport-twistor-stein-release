import TransportOkaGrauert.ChartOrbits
import TransportOkaGrauert.PathContinuation

/-! Smoothness of geodesic differentiation in the conformal chart, up to the boundary. -/
noncomputable section
namespace TransportOkaGrauert.ChartRegularity

open SimpleDiskTarget ChartOrbits PathContinuation Metric Filter
open scoped ContDiff Topology

/-- Smoothness of the lifted conformal geodesic vector needs only the germ of
the conformal factor at the base point. -/
theorem chartVector_contDiffAt {lam : ℂ → ℝ} (p : ℂ × ℝ)
    (h : ContDiffAt ℝ ∞ lam p.1) : ContDiffAt ℝ ∞ (chartVector lam) p := by
  have hv : ContDiff ℝ ∞ (fun t : ℝ => (Circle.exp t : ℂ)) := by
    simp only [Circle.coe_exp]
    exact (Complex.ofRealCLM.contDiff.mul contDiff_const).cexp
  have hw := hv.contDiffAt.comp p (contDiffAt_snd (𝕜 := ℝ))
  have hd := (h.fderiv_right (m := ∞) (by simp)).comp p contDiffAt_fst
  have hdir (v : ℂ) : ContDiffAt ℝ ∞ (fun q : ℂ × ℝ => fderiv ℝ lam q.1 v) p :=
    hd.clm_apply contDiffAt_const
  have hre := Complex.reCLM.contDiff.contDiffAt.comp p hw
  have him := Complex.imCLM.contDiff.contDiffAt.comp p hw
  exact ((h.comp p contDiffAt_fst).neg.exp).smul
    (hw.prodMk (((hdir Complex.I).mul hre).sub ((hdir 1).mul him)))

/-- The chart geodesic derivative preserves smoothness up to the closed base
disk. Ambient smoothness of the metric is needed only at points of the disk. -/
theorem smooth_chartX {n : ℕ} {lam : ℂ → ℝ} {F : Field n}
    (hlam : ∀ z ∈ closedBall (0 : ℂ) 1, ContDiffAt ℝ ∞ lam z)
    (hF : SmoothToBoundary F) : SmoothToBoundary (chartX lam F) := by
  intro z hz θ i j
  let f (p : ℂ × ℝ) := F p.1 (Circle.exp p.2) i j
  have hf : ContDiffAt ℝ ∞ f (z, θ) := hF z hz θ i j
  have hdir := (hf.fderiv_right (m := ∞) (by simp)).clm_apply
    (chartVector_contDiffAt (z, θ) (hlam z hz))
  apply hdir.congr_of_eventuallyEq
  filter_upwards [(hf.of_le (show 1 ≤ (∞ : WithTop ℕ∞) by decide)).eventually (by decide)]
    with p hp
  exact geodesicX_eq_chart_derivative lam _ p.1 p.2 (hp.differentiableAt one_ne_zero)

end TransportOkaGrauert.ChartRegularity
