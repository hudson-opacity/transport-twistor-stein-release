import TransportOkaGrauert.ScalarGeneralKernelJoint
import TransportOkaGrauert.SmoothRadialHessian

/-! # Radial and angular columns of the joint geodesic exponential

The pulled-back conformal metric obeys the Gauss lemma and has a smooth
rank-one transverse defect in Cartesian velocity coordinates. -/

noncomputable section
namespace TransportOkaGrauert.ScalarGeneralKernel
open Complex Metric Set Filter SimpleRadialVariation ConformalFrame SimpleDiskTarget
open scoped ContDiff Topology

def dot (u v : ℂ) : ℝ := u.re*v.re+u.im*v.im
def wedge (u v : ℂ) : ℝ := u.re*v.im - u.im*v.re

private theorem dot_I (u : ℂ) : dot u (I*u) = 0 := by simp [dot]; ring
private theorem dot_self (u : ℂ) : dot u u = Complex.normSq u := rfl
theorem wedge_I (u : ℂ) : wedge u (I*u) = Complex.normSq u := by simp [wedge,normSq_apply]
private theorem dot_scale (s t : ℝ) (u v : ℂ) : dot (s • u) (t • v) = s*t*dot u v := by
  simp [dot,real_smul]; ring
theorem wedge_scale (s t : ℝ) (u v : ℂ) : wedge (s • u) (t • v) = s*t*wedge u v := by
  simp [wedge,real_smul]; ring

private theorem linear_apply (M : ℂ →L[ℝ] ℂ) (u : ℂ) : M u = u.re • M 1 + u.im • M I := by
  rw [← M.map_smul,← M.map_smul,← map_add]
  congr 1
  simp [Complex.real_smul]

theorem wedge_linear (M : ℂ →L[ℝ] ℂ) (u v : ℂ) : wedge (M u) (M v) = M.det * wedge u v := by
  rw [linear_apply M u,linear_apply M v,determinant_formula]
  simp [wedge,Complex.real_smul]; ring

theorem polar_jacobi_with_direction {σ : ℂ → ℝ} {a : ℂ} (C : Coordinates σ a) (simple : SimpleMetric σ)
    {x : ℂ} (ret : x ∈ SimpleRadialStar.retained C.endpoint 1) (nx : x ≠ 0) :
    let w := Circle.exp (C.flow (x.arg,‖x‖)).2.1
    ∃ j : ℝ, 0 < j ∧
      fderiv ℝ C.endpoint x x = (‖x‖*Real.exp (-σ (C.endpoint x))) • (w:ℂ) ∧
      fderiv ℝ C.endpoint x (I*x) = (j*Real.exp (-σ (C.endpoint x))) • (I*(w:ℂ)) := by
  let r := ‖x‖
  let α := x.arg
  let d : ℂ := Circle.exp α
  have hr : 0 < r := norm_pos_iff.mpr nx
  have repr : r • d = x := polar_angle x
  have temp (s : ℝ) (hs : s ∈ Icc 0 r) : ‖(C.flow (α,s)).1‖ ≤ 1 := by
    rw [C.polar]
    have eq : s • d = (s/r) • x := by rw [← repr,smul_smul,div_mul_cancel₀ _ hr.ne']
    rw [show (Circle.exp α:ℂ) = d from rfl,eq]
    exact ret _ ⟨div_nonneg hs.1 hr.le,(div_le_one hr).mpr hs.2⟩
  have ini : fderiv ℝ C.flow (α,0) (1,0) = V (C.flow (α,0)) := by
    have line := (hasDerivAt_id α).prodMk (hasDerivAt_const α (0:ℝ))
    have act := (C.flow_smooth.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt α line
    exact act.unique (((hasDerivAt_const α a).prodMk ((hasDerivAt_id α).prodMk (hasDerivAt_const α (0:ℝ)))).congr_of_eventuallyEq (.of_forall C.initial))
  obtain ⟨geo,j,dj,jac,j0,j1,angular⟩ := jacobi_of_flow simple.smooth hr.le C.flow
    (fun _ _ => C.flow_smooth.contDiffAt) (fun t ht => C.ode _ (temp t ht)) ini
  have jp := ChartJacobi.normalized_jacobi_positive simple hr geo
    (fun t ht => mem_closedBall_zero_iff.mpr (temp t ht)) jac j0 j1
  let w := Circle.exp (C.flow (α,r)).2.1
  have ep : (C.flow (α,r)).1 = C.endpoint x := (C.polar α r).trans (congrArg C.endpoint repr)
  refine ⟨j r,jp,?_,?_⟩
  · have eq : fderiv ℝ C.flow (α,r) (0,1) = X σ (C.flow (α,r)) :=
      (C.ode _ (temp r (right_mem_Icc.mpr hr.le))).self_of_nhds
    have base := (ContinuousLinearMap.fst ℝ ℂ (ℝ × ℝ)).hasFDerivAt.comp_hasDerivAt r
      ((C.flow_smooth.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt r
        ((hasDerivAt_const r α).prodMk (hasDerivAt_id r)))
    have act := (C.endpoint_smooth.differentiable (by simp) (r • d)).hasFDerivAt.comp_hasDerivAt r
      ((hasDerivAt_id r).smul_const d)
    have h := act.unique (base.congr_of_eventuallyEq (.of_forall (fun s => (C.polar α s).symm)))
    change fderiv ℝ C.endpoint (r • d) ((1:ℝ) • d) = (fderiv ℝ C.flow (α,r) (0,1)).1 at h
    rw [repr,one_smul,eq,(chart_columns σ (C.flow (α,r))).1,ep] at h
    change fderiv ℝ C.endpoint x d = Real.exp (-σ (C.endpoint x)) • (w:ℂ) at h
    calc
      _ = r • fderiv ℝ C.endpoint x d := by rw [← map_smul,repr]
      _ = _ := by rw [h,smul_smul]
  · have base := (ContinuousLinearMap.fst ℝ ℂ (ℝ × ℝ)).hasFDerivAt.comp_hasDerivAt α
      ((C.flow_smooth.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt α
        ((hasDerivAt_id α).prodMk (hasDerivAt_const α r)))
    have act := (C.endpoint_smooth.differentiable (by simp) (r • d)).hasFDerivAt.comp_hasDerivAt α
      ((angle_velocity α).const_smul r)
    have eq := act.unique (base.congr_of_eventuallyEq (.of_forall (fun s => (C.polar s r).symm)))
    have quarter : r • (I*d) = I*x := by rw [← mul_smul_comm,repr]
    change fderiv ℝ C.endpoint (r • d) (r • (I*d)) = (fderiv ℝ C.flow (α,r) (1,0)).1 at eq
    rw [repr,quarter] at eq
    exact eq.trans (by simpa [ep,w] using angular r (right_mem_Icc.mpr hr.le))

theorem polar_jacobi {σ : ℂ → ℝ} {a : ℂ} (C : Coordinates σ a) (simple : SimpleMetric σ)
    {x : ℂ} (ret : x ∈ SimpleRadialStar.retained C.endpoint 1) (nx : x ≠ 0) :
    ∃ w : Circle, ∃ j : ℝ, 0 < j ∧
      fderiv ℝ C.endpoint x x = (‖x‖*Real.exp (-σ (C.endpoint x))) • (w:ℂ) ∧
      fderiv ℝ C.endpoint x (I*x) = (j*Real.exp (-σ (C.endpoint x))) • (I*(w:ℂ)) :=
  ⟨_,polar_jacobi_with_direction C simple ret nx⟩

def defect (M : ℂ →L[ℝ] ℂ) (c : ℝ) (u v : ℂ) := c * dot (M u) (M v) - dot u v

theorem defect_radial {σ : ℂ → ℝ} {a : ℂ} (C : Coordinates σ a) (simple : SimpleMetric σ)
    {x : ℂ} (hx : x ∈ SimpleRadialStar.retained C.endpoint 1) :
    let M := fderiv ℝ C.endpoint x
    let c := Real.exp (2 * σ (C.endpoint x))
    defect M c 1 1 * x.re + defect M c 1 I * x.im = 0 ∧
    defect M c 1 I * x.re + defect M c I I * x.im = 0 := by
  intro M c
  by_cases nx : x = 0
  · simp [nx]
  obtain ⟨w,j,_,rad,ang⟩ := polar_jacobi C simple hx nx
  have hunit : Complex.normSq (w:ℂ) = 1 := by simp [Complex.normSq_eq_norm_sq]
  have cancel : c * (Real.exp (-σ (C.endpoint x)))^2 = 1 := by
    dsimp [c]
    rw [← Real.exp_nat_mul,← Real.exp_add]
    ring_nf; simp
  have rr : defect M c x x = 0 := by
    change c * dot (fderiv ℝ C.endpoint x x) (fderiv ℝ C.endpoint x x) - dot x x = 0
    rw [rad,dot_scale,dot_self,dot_self,hunit,Complex.normSq_eq_norm_sq]
    nlinarith [congrArg (fun u : ℝ => u*‖x‖^2) cancel]
  have rt : defect M c x (I*x) = 0 := by
    change c * dot (fderiv ℝ C.endpoint x x) (fderiv ℝ C.endpoint x (I*x)) - dot x (I*x) = 0
    rw [rad,ang,dot_scale,dot_I,dot_I]; ring
  let l := defect M c 1 1
  let m := defect M c 1 I
  let n := defect M c I I
  let u := l*x.re+m*x.im
  let v := m*x.re+n*x.im
  have a₁ : x.re*u+x.im*v = 0 := by
    convert rr using 1
    simp only [u,v,l,m,n,defect,linear_apply M x,dot,Complex.real_smul]
    simp; ring
  have a₂ : -x.im*u+x.re*v = 0 := by
    convert rt using 1
    simp only [u,v,l,m,n,defect,linear_apply M x,linear_apply M (I*x),dot,Complex.real_smul]
    simp; ring
  have hp : x.re^2+x.im^2 ≠ 0 := by
    have h := (sq_pos_of_pos (norm_pos_iff.mpr nx)).ne'
    rwa [← Complex.normSq_eq_norm_sq,Complex.normSq_apply,← pow_two,← pow_two] at h
  constructor
  · change u = 0
    apply (mul_eq_zero.mp (show (x.re^2+x.im^2)*u=0 by linear_combination x.re*a₁-x.im*a₂)).resolve_left hp
  · change v = 0
    apply (mul_eq_zero.mp (show (x.re^2+x.im^2)*v=0 by linear_combination x.im*a₁+x.re*a₂)).resolve_left hp

end TransportOkaGrauert.ScalarGeneralKernel
