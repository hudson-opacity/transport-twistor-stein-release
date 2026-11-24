import TransportOkaGrauert.ScalarGeneralKernelFamily
import TransportOkaGrauert.ScalarGeneralKernelAmplitude

/-! # Joint smoothness of the curved X-ray kernel away from the diagonal -/

noncomputable section
namespace TransportOkaGrauert.ScalarGeneralKernel
open Complex Metric Set Filter
open scoped ContDiff Topology

def verticalDerivative (L : ℂ × ℂ → ℂ) (q : ℂ × ℂ) : ℂ →L[ℝ] ℂ :=
  (fderiv ℝ L q).comp (.inr ℝ ℂ ℂ)

def jointDensity (L : ℂ × ℂ → ℂ) (q : ℂ × ℂ) : ℝ := |(verticalDerivative L q).det| / ‖L q‖

theorem verticalDerivative_eq {L : ℂ × ℂ → ℂ} {a y : ℂ} (h : DifferentiableAt ℝ L (a,y)) :
    verticalDerivative L (a,y) = fderiv ℝ (fun x => L (a,x)) y :=
  (h.hasFDerivAt.comp y ((hasFDerivAt_const a y).prodMk (hasFDerivAt_id y))).fderiv.symm

private theorem smooth_det_at {M : ℂ × ℂ → ℂ →L[ℝ] ℂ} {q : ℂ × ℂ} (s : ContDiffAt ℝ ∞ M q) :
    ContDiffAt ℝ ∞ (fun z => (M z).det) q := by
  simp_rw [determinant_formula]
  have apply (v : ℂ) : ContDiffAt ℝ ∞ (fun z => M z v) q := s.clm_apply contDiffAt_const
  exact ((reCLM.contDiff.contDiffAt.comp q (apply 1)).mul (imCLM.contDiff.contDiffAt.comp q (apply I))).sub
    ((reCLM.contDiff.contDiffAt.comp q (apply I)).mul (imCLM.contDiff.contDiffAt.comp q (apply 1)))

private theorem Coordinates.log_regular {σ : ℂ → ℝ} {a : ℂ} (C : Coordinates σ a)
    {y : ℂ} (hy : y ∈ ball (0:ℂ) 1) : (fderiv ℝ C.logMap y).det ≠ 0 := by
  have hd := ((C.log_smooth y hy).contDiffAt (isOpen_ball.mem_nhds hy)).differentiableAt (by simp)
  have d := (C.endpoint_smooth.differentiable (by simp) _).hasFDerivAt.comp y hd.hasFDerivAt
  have h : C.endpoint ∘ C.logMap =ᶠ[𝓝 y] id := by
    filter_upwards [isOpen_ball.mem_nhds hy] with z hz using (C.right z hz).2
  have eq := d.unique ((hasFDerivAt_id y).congr_of_eventuallyEq h)
  have inj : Function.Injective (fderiv ℝ C.logMap y) := by
    intro v w e
    have ev := DFunLike.congr_fun eq v
    have ew := DFunLike.congr_fun eq w
    change fderiv ℝ C.endpoint _ (fderiv ℝ C.logMap y v) = v at ev
    change fderiv ℝ C.endpoint _ (fderiv ℝ C.logMap y w) = w at ew
    exact ev.symm.trans ((congrArg _ e).trans ew)
  intro bad
  exact (LinearMap.det_eq_zero_iff_ker_ne_bot.mp bad) (LinearMap.ker_eq_bot.mpr inj)

/-- Jointly smooth off-diagonal Euclidean-area density of the ray average on
a simple disk. -/
theorem exists_joint_kernel {σ : ℂ → ℝ} (simple : SimpleDiskTarget.SimpleMetric σ) :
    ∃ E L : ℂ × ℂ → ℂ, ContDiff ℝ ∞ E ∧
      ContDiffOn ℝ ∞ L (ball (0:ℂ) 1 ×ˢ ball (0:ℂ) 1) ∧
      ContDiffOn ℝ ∞ (jointDensity L) {q | q.1 ∈ ball (0:ℂ) 1 ∧ q.2 ∈ ball (0:ℂ) 1 ∧ q.1 ≠ q.2} ∧
      ∀ a ∈ ball (0:ℂ) 1, ∃ C : Coordinates σ a,
        C.endpoint = (fun v => E (a,v)) ∧ C.logMap = (fun y => L (a,y)) ∧
        ∀ y ∈ ball (0:ℂ) 1, C.density y = jointDensity L (a,y) := by
  let B := ball (0:ℂ) 1
  obtain ⟨E,L,sE,sL,fam⟩ := joint_coordinates simple
  have smooth (a y : ℂ) (ha : a ∈ B) (hy : y ∈ B) : ContDiffAt ℝ ∞ L (a,y) :=
    (sL _ ⟨ha,hy⟩).contDiffAt ((isOpen_ball.prod isOpen_ball).mem_nhds ⟨ha,hy⟩)
  refine ⟨E,L,sE,sL,?_,?_⟩
  · rintro ⟨a,y⟩ ⟨ha,hy,ne⟩
    obtain ⟨C,_,t⟩ := fam a ha
    have s := smooth a y ha hy
    have sv : ContDiffAt ℝ ∞ (verticalDerivative L) (a,y) :=
      (s.fderiv_right (m := ∞) (by simp)).clm_comp contDiffAt_const
    have eq := verticalDerivative_eq (s.differentiableAt (by simp))
    rw [← t] at eq
    have nz : L (a,y) ≠ 0 := by
      intro h
      have : C.logMap y = 0 := (congrFun t y).trans h
      exact ne (C.endpoint_zero.symm.trans ((congrArg C.endpoint this).symm.trans (C.right y hy).2))
    have sabs : ContDiffAt ℝ ∞ (fun p => |(verticalDerivative L p).det|) (a,y) := by
      simpa only [Real.norm_eq_abs] using (smooth_det_at sv).norm ℝ (eq ▸ C.log_regular hy)
    exact (sabs.div (s.norm ℝ nz) (norm_ne_zero_iff.mpr nz)).contDiffWithinAt
  · intro a ha
    obtain ⟨C,f,t⟩ := fam a ha
    refine ⟨C,f,t,fun y hy => ?_⟩
    rw [Coordinates.density,jointDensity,verticalDerivative_eq ((smooth a y ha hy).differentiableAt (by simp)),t]

end TransportOkaGrauert.ScalarGeneralKernel
