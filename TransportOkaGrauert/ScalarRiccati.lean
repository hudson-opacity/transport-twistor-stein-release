import TransportOkaGrauert.PhysicalJacobiWeight
import TransportOkaGrauert.ScalarPestov

/-! # A strict periodic Riccati supersolution in the conformal chart -/
noncomputable section
namespace TransportOkaGrauert.ScalarPestov
open Complex SimpleDiskTarget PhysicalJacobiWeight PathContinuation PolarCollar
open FrameLevi ConformalFrame GeodesicFlowExtension Filter
open scoped ContDiff Topology

theorem strict_riccati {σ : ℂ → ℝ} (simple : SimpleMetric σ) :
    ∃ r : Chart → ℝ, (∀ p, r (p+(0,2*Real.pi,0)) = r p) ∧
      ∀ p, ‖p.1‖ ≤ 1 → ContDiffAt ℝ ∞ r p ∧ speed σ r p + r p ^ 2 + curvature σ p.1 < 0 := by
  obtain ⟨h,per,good⟩ := exists_global_weight simple
  let W := chartVector σ
  let g := along W h
  let r := fun p : Chart => -g (direction p)
  have push (p : Chart) : direction (X σ p) = W (direction p) :=
    congrFun (projected_X σ) (direction p)
  have hw (q : State) : ContDiffAt ℝ ∞ W q := ChartRegularity.chartVector_contDiffAt q simple.smooth.contDiffAt
  have dg (p : Chart) (hp : ‖p.1‖ ≤ 1) : ContDiffAt ℝ ∞ g (direction p) :=
    ((good _ hp).1.fderiv_right (m := ∞) (by simp)).clm_apply (hw _)
  let c : State := (0,2*Real.pi)
  have trans : (fun y => h (y+c)) = h := by
    funext y
    have ey : y+c = (y.1,y.2+2*Real.pi) := Prod.ext (add_zero _) rfl
    rw [ey]
    exact per y.1 _ _ (by simp [Circle.exp_add])
  have tw (q : State) : W (q+c) = W q := by simp [W,c,chartVector,Circle.exp_add,Circle.exp_two_pi]
  have tg (q : State) : g (q+c) = g q := by
    have d : fderiv ℝ h (q+c) = fderiv ℝ h q := by rw [← fderiv_comp_add_right,trans]
    simp [g,along,d,tw]
  refine ⟨r,fun p => congrArg Neg.neg (tg (direction p)),?_⟩
  intro p hp
  have d := dg p hp
  refine ⟨(d.comp p direction.contDiff.contDiffAt).neg,?_⟩
  have eq : speed σ r p = -along W g (direction p) := by
    change fderiv ℝ (fun y => -g (direction y)) p (X σ p) = _
    rw [fderiv_fun_neg,show fderiv ℝ (fun y => g (direction y)) p = _ from
      ((d.differentiableAt (by simp)).hasFDerivAt.comp p direction.hasFDerivAt).fderiv]
    simp [along,push]
  have pos := (good (direction p) hp).2
  change 0 < along W g (direction p) - curvature σ p.1 - g (direction p)^2 at pos
  rw [eq]
  change -along W g (direction p) + (-g (direction p))^2 + _ < 0
  nlinarith

end TransportOkaGrauert.ScalarPestov
