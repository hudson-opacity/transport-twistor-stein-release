import TransportOkaGrauert.ScalarReachableTrace
import TransportOkaGrauert.ScalarDiskHilbert
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-! # The reachable real subspace and its smooth annihilator -/
noncomputable section
namespace TransportOkaGrauert.ScalarReachableHilbert
open ScalarDiskHilbert ScalarReachableTrace ScalarRayPairing SimpleDiskTarget
open ScalarGeneralTransport ChartCoefficients Set Metric MeasureTheory Filter Complex
open scoped ContDiff Topology RealInnerProductSpace

/-- Classes of globally smooth real base functions which agree on the smaller
disk with the normalized mean of a smooth invariant trace there. -/
def reachable (σ : ℂ → ℝ) (r : ℝ) : Submodule ℝ H where
  carrier := {x | ∃ (a : ℂ → ℝ) (ha : ContDiff ℝ ∞ a), ofSmooth a ha = x ∧
    Reachable σ r (fun z => (a z : ℂ))}
  zero_mem' := by
    refine ⟨fun _ => 0,contDiff_const,?_,ScalarReachableTrace.zero σ r⟩
    apply Lp.ext
    exact (ofSmooth_coeFn _ contDiff_const).trans (Lp.coeFn_zero ..).symm
  add_mem' := by
    rintro x y ⟨a,ha,rfl,ra⟩ ⟨b,hb,rfl,rb⟩
    refine ⟨a+b,ha.add hb,?_,?_⟩
    · apply Lp.ext
      exact (ofSmooth_coeFn _ _).trans (((ofSmooth_coeFn a ha).add
        (ofSmooth_coeFn b hb)).symm.trans (Lp.coeFn_add _ _).symm)
    · apply ScalarReachableTrace.congr (lincomb ra rb 1 1)
      intro z _; simp
  smul_mem' := by
    rintro k x ⟨a,ha,rfl,ra⟩
    have hs : ContDiff ℝ ∞ (k • a) := contDiff_const.smul ha
    refine ⟨k • a,hs,?_,?_⟩
    · apply Lp.ext
      filter_upwards [ofSmooth_coeFn _ hs, Lp.coeFn_smul k (ofSmooth a ha),ofSmooth_coeFn a ha] with z es he ea
      simp [es,he,ea]
    · apply ScalarReachableTrace.congr (lincomb ra ra (k:ℂ) 0)
      intro z _; simp

theorem ofSmooth_mem {σ r} {a : ℂ → ℝ} (ha : ContDiff ℝ ∞ a)
    (h : Reachable σ r (fun z => (a z : ℂ))) : ofSmooth a ha ∈ reachable σ r := ⟨a,ha,rfl,h⟩

theorem inner_smooth (c a : ℂ → ℝ) (hc : ContDiff ℝ ∞ c) (ha : ContDiff ℝ ∞ a) :
    inner ℝ (ofSmooth c hc) (ofSmooth a ha) = ∫ z in ball (0:ℂ) 1, c z * a z := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ofSmooth_coeFn c hc,ofSmooth_coeFn a ha] with z ez ea
  simp [ez,ea,mul_comm]

theorem reachable_of_ofSmooth_mem {σ r a} (hr : r ≤ 1) (ha : ContDiff ℝ ∞ a)
    (mem : ofSmooth a ha ∈ reachable σ r) : Reachable σ r (fun z => (a z : ℂ)) := by
  obtain ⟨b,hb,e,rb⟩ := mem
  have eq : b =ᵐ[μ] a := (ofSmooth_coeFn b hb).symm.trans (e ▸ ofSmooth_coeFn a ha)
  have ev := Measure.eqOn_open_of_ae_eq eq isOpen_ball hb.continuous.continuousOn ha.continuous.continuousOn
  apply ScalarReachableTrace.congr rb
  intro z hz; exact congrArg Complex.ofReal (ev (ball_subset_ball hr hz))

theorem annihilator {σ : ℂ → ℝ} (simple : SimpleMetric σ) {r : ℝ} (hr : 0 < r) (hr₁ : r < 1)
    (x : H) (sx : x ∈ smooth) (ox : x ∈ (reachable σ r)ᗮ) : x = 0 := by
  obtain ⟨c,hc,ec⟩ := (mem_smooth_iff x).mp sx
  have pairing (a : ℂ → ℝ) (ha : ContDiff ℝ ∞ a) (ra : Reachable σ r (fun z => (a z : ℂ))) :
      (∫ z in ball (0:ℂ) 1, c z * a z) = 0 := by
    rw [← inner_smooth c a hc ha,ec]
    exact ((reachable σ r).mem_orthogonal' x).mp ox _ (ofSmooth_mem ha ra)
  let η := fun z : ℂ => Real.smoothTransition (normSq z-r^2)
  have hsq : ContDiff ℝ ∞ normSq := by
    have eq : normSq = fun z : ℂ => z.re^2 + z.im^2 := by funext z; simp [Complex.normSq_apply,pow_two]
    rw [eq]; exact (reCLM.contDiff.pow 2).add (imCLM.contDiff.pow 2)
  have hη : ContDiff ℝ ∞ η := Real.smoothTransition.contDiff.comp (hsq.sub contDiff_const)
  have small (z : ℂ) (hz : ‖z‖ ≤ r) : η z = 0 := by
    apply Real.smoothTransition.zero_of_nonpos
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [sq_nonneg (r-‖z‖),norm_nonneg z]
  have large (z : ℂ) (hz : r < ‖z‖) : 0 < η z := by
    apply Real.smoothTransition.pos_of_pos
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [mul_pos (sub_pos.mpr hz) (add_pos_of_nonneg_of_pos (norm_nonneg z) hr)]
  have ra : Reachable σ r (fun z => ((c z * η z : ℝ) : ℂ)) := by
    apply ScalarReachableTrace.congr (ScalarReachableTrace.zero _ _)
    intro z hz; simp [small z (mem_ball_zero_iff.mp hz).le]
  have integral0 := pairing (fun z => c z * η z) (hc.mul hη) ra
  let E := fun z => c z * (c z * η z)
  have ce : Continuous E := hc.continuous.mul (hc.continuous.mul hη.continuous)
  have ie : Integrable E μ :=
    (ce.continuousOn.integrableOn_compact (isCompact_closedBall (0:ℂ) 1)).mono_set ball_subset_closedBall
  have pos (z : ℂ) : 0 ≤ E z := by
    dsimp only [E]; rw [← mul_assoc]; exact mul_nonneg (mul_self_nonneg _) (Real.smoothTransition.nonneg _)
  have ae := (integral_eq_zero_iff_of_nonneg pos ie).mp integral0
  have ez := Measure.eqOn_open_of_ae_eq ae isOpen_ball ce.continuousOn continuousOn_const
  have ann (z : ℂ) (hout : r < ‖z‖) (hin : ‖z‖ < 1) : c z = 0 := by
    have e := ez (mem_ball_zero_iff.mpr hin)
    change c z * (c z * η z) = 0 at e
    rcases mul_eq_zero.mp e with e|e
    · exact e
    · exact (mul_eq_zero.mp e).resolve_right (large z hout).ne'
  let β : ContDiffBump (0:ℂ) := ⟨(r+1)/2,1,by linarith,by linarith⟩
  let c' := fun z => β z * c z
  have sc' : ContDiff ℝ ∞ c' := β.contDiff.mul hc
  have same (z : ℂ) (hz : z ∈ ball (0:ℂ) 1) : c' z = c z := by
    by_cases h : ‖z‖ ≤ r
    · have e := β.one_of_mem_closedBall (x := z) (by simp only [mem_closedBall,dist_zero_right]; change ‖z‖ ≤ (r+1)/2; linarith)
      simp [c',e]
    · simp [c',ann z (lt_of_not_ge h) (mem_ball_zero_iff.mp hz)]
  have off (z : ℂ) (hrz : r < ‖z‖) : c' z = 0 := by
    by_cases hz : ‖z‖ < 1
    · simp [c',ann z hrz hz]
    · have eq := β.zero_of_le_dist (x := z) (by simpa [β] using le_of_not_gt hz)
      simp [c',eq]
  have c0 := annihilator_eq_zero simple hr hr₁ sc' off (fun a ha _ H => by
    have e := pairing a ha H
    rw [← e]
    exact setIntegral_congr_fun measurableSet_ball (fun z hz => congrArg (fun t => t * a z) (same z hz)))
  rw [← ec]
  apply Lp.ext
  filter_upwards [ofSmooth_coeFn c hc,Lp.coeFn_zero ℝ 2 μ,ae_mem_disk] with z hc' hz hm
  rw [hc',hz]
  exact (same z hm).symm.trans (congrFun c0 z)

theorem realize_complex {σ : ℂ → ℝ} {r : ℝ} (hr : r ≤ 1) (range : smooth ≤ reachable σ r)
    (a : ℂ → ℂ) (ha : ContDiff ℝ ∞ a) : Reachable σ r a := by
  apply complex_of_real _ a ha
  intro v hv
  exact reachable_of_ofSmooth_mem hr hv (range ((mem_smooth_iff _).mpr ⟨v,hv,rfl⟩))

theorem local_mean (range : ∀ (σ : ℂ → ℝ), SimpleMetric σ → ∀ r : ℝ, 0 < r → r < 1 → smooth ≤ reachable σ r) :
    SteinMomentBridge.LocalMeanStatement := by
  intro σ simple a ha r hr hr₁
  obtain ⟨h,sh,xh,eh⟩ := realize_complex hr₁.le (range σ simple r hr hr₁) a ha
  exact ⟨h,fun _ _ _ => sh.contDiffAt,xh,eh⟩

end TransportOkaGrauert.ScalarReachableHilbert
