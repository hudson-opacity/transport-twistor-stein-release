import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Tactic

/-! Differentiation under a compact angular integral from C¹ at each point
of the fiber. Compactness produces one common base neighborhood and one
dominating constant even when the base point lies at the chart boundary. -/
noncomputable section
namespace TransportOkaGrauert.CoefficientIntegral
open Complex Metric MeasureTheory Set Filter
open scoped Topology Interval ContDiff

private abbrev incl : ℂ →L[ℝ] ℂ × ℝ := ContinuousLinearMap.inl ℝ ℂ ℝ

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def baseDerivative (g : ℂ × ℝ → E) (p : ℂ × ℝ) : ℂ →L[ℝ] E :=
  (fderiv ℝ g p).comp incl

theorem slice_hasFDeriv {g : ℂ × ℝ → E} {p : ℂ × ℝ} (h : ContDiffAt ℝ 1 g p) :
    HasFDerivAt (fun z => g (z, p.2)) (baseDerivative g p) p.1 := by
  have he : HasFDerivAt (fun z : ℂ => (z, p.2)) incl p.1 :=
    (hasFDerivAt_id _).prodMk (hasFDerivAt_const _ _)
  exact (h.differentiableAt (by decide)).hasFDerivAt.comp p.1 he

theorem baseDerivative_cont {g : ℂ × ℝ → E} {p : ℂ × ℝ} (h : ContDiffAt ℝ 1 g p) :
    ContinuousAt (baseDerivative g) p :=
  (h.continuousAt_fderiv (by decide)).clm_comp continuousAt_const

/-- Differentiate the base variable inside a finite ordinary angular integral.
The resulting derivative is the integral of the actual base partial
derivative. The interval integral is taken with respect to Lebesgue measure. -/
theorem interval_derivative [CompleteSpace E] (g : ℂ × ℝ → E) (z : ℂ) {T : ℝ} (hT : 0 < T)
    (hg : ∀ t ∈ Icc 0 T, ContDiffAt ℝ 1 g (z, t)) :
    HasFDerivAt (fun p => ∫ t in (0 : ℝ)..T, g (p,t))
      (∫ t in (0 : ℝ)..T, fderiv ℝ (fun p => g (p,t)) z) z ∧
    IntervalIntegrable (fun t => fderiv ℝ (fun p => g (p,t)) z) volume 0 T := by
  let good := {p : ℂ × ℝ | ContDiffAt ℝ 1 g p}
  have hopen : IsOpen good := isOpen_iff_mem_nhds.mpr fun p hp =>
    (show ContDiffAt ℝ 1 g p from hp).eventually (by decide)
  have hsub : ({z} : Set ℂ) ×ˢ Icc 0 T ⊆ good := by
    rintro ⟨p, t⟩ ⟨rfl, ht⟩
    exact hg t ht
  obtain ⟨u, v, hu, _, hzu, hv, huv⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_Icc hopen hsub
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hu.mem_nhds (hzu (mem_singleton z)))
  let K := closedBall z r ×ˢ Icc (0 : ℝ) T
  have hK : IsCompact K := (isCompact_closedBall z r).prod isCompact_Icc
  have hok (p : ℂ × ℝ) (hp : p ∈ K) : ContDiffAt ℝ 1 g p := huv ⟨hball hp.1, hv hp.2⟩
  have hcont : ContinuousOn (fun p => ‖baseDerivative g p‖) K :=
    fun p hp => (baseDerivative_cont (hok p hp)).norm.continuousWithinAt
  obtain ⟨C,hC⟩ := hK.bddAbove_image hcont
  have hzball : z ∈ closedBall z r := mem_closedBall_self hr.le
  have contg (p : ℂ) (hp : p ∈ closedBall z r) :
      ContinuousOn (fun t => g (p,t)) (Icc 0 T) :=
    fun t ht => ((hok (p,t) ⟨hp,ht⟩).continuousAt.comp (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
  have contd : ContinuousOn (fun t => baseDerivative g (z,t)) (Icc 0 T) :=
    fun t ht => ((baseDerivative_cont (hg t ht)).comp (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
  have intd : IntervalIntegrable (fun t => baseDerivative g (z,t)) volume 0 T :=
    contd.intervalIntegrable_of_Icc hT.le
  have H : HasFDerivAt (fun p => ∫ t in (0 : ℝ)..T, g (p,t))
      (∫ t in (0 : ℝ)..T, baseDerivative g (z,t)) z := by
    apply hasFDerivAt_integral_of_dominated_of_fderiv_le'' (s := closedBall z r)
      (F' := fun p t => baseDerivative g (p,t)) (bound := fun _ => C) (closedBall_mem_nhds z hr)
    · filter_upwards [closedBall_mem_nhds z hr] with p hp
      rw [uIoc_of_le hT.le]
      exact ((contg p hp).mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
    · exact (contg z hzball).intervalIntegrable_of_Icc hT.le
    · rw [uIoc_of_le hT.le]
      exact (contd.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
    · rw [uIoc_of_le hT.le]
      filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with t ht
      intro p hp
      exact hC ⟨(p,t), ⟨hp, Ioc_subset_Icc_self ht⟩, rfl⟩
    · exact intervalIntegrable_const
    · rw [uIoc_of_le hT.le]
      filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with t ht
      intro p hp
      exact slice_hasFDeriv (hok (p,t) ⟨hp, Ioc_subset_Icc_self ht⟩)
  have he (t : ℝ) (ht : t ∈ uIcc 0 T) : baseDerivative g (z,t) =
      fderiv ℝ (fun p => g (p,t)) z :=
    (slice_hasFDeriv (hg t ((uIcc_of_le hT.le) ▸ ht))).fderiv.symm
  rw [intervalIntegral.integral_congr he] at H
  exact ⟨H, (contd.congr fun t ht => (he t ((uIcc_of_le hT.le).symm ▸ ht)).symm).intervalIntegrable_of_Icc hT.le⟩

end TransportOkaGrauert.CoefficientIntegral
