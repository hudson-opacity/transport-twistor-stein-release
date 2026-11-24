import TransportOkaGrauert.PhysicalJacobiWeight
import TransportOkaGrauert.PhysicalSteinCollar
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-! # A proper physical exhaustion on every simple transport disk

Insert the periodic Jacobi weight only at nonzero velocities and glue the
resulting strict velocity collar to the physical logarithmic base barrier.
The Cartesian potential is smooth across the angular branch cut and the
zero section. Its exterior Levi form is positive outside a compact set.
-/

noncomputable section
namespace TransportOkaGrauert.PhysicalStein

open Set Filter Metric Complex ChartStein CollarGluing FrameLevi PolarCR
open PhysicalJacobiWeight ConformalCollar
open scoped ContDiff Topology

private def cutoff (w : ℂ) := Real.smoothTransition (4*normSq w - 1)
private def weighted (h : ℂ × ℝ → ℝ) (p : E) := diskBarrier p.2 + cutoff p.2 * h (p.1,p.2.arg)

private theorem smooth_cutoff : ContDiff ℝ ∞ cutoff := by
  have ds : ContDiff ℝ ∞ normSq := by
    have eq : normSq = fun z : ℂ => z.re^2 + z.im^2 := by funext z; simp [Complex.normSq_apply,pow_two]
    rw [eq]; exact (reCLM.contDiff.pow 2).add (imCLM.contDiff.pow 2)
  exact Real.smoothTransition.contDiff.comp ((contDiff_const.mul ds).sub contDiff_const)

private theorem arg_shift {v w : ℂ} (hv : v ≠ 0) (hw : w ≠ 0) :
    Circle.exp ((v/w).arg + w.arg) = Circle.exp v.arg := by
  change Real.Angle.toCircle (((v/w).arg + w.arg : ℝ):Real.Angle) = Real.Angle.toCircle (v.arg:Real.Angle)
  apply congrArg Real.Angle.toCircle
  rw [Real.Angle.coe_add,Complex.arg_div_coe_angle hv hw,sub_add_cancel]

private theorem weighted_smooth {h : ℂ × ℝ → ℝ}
    (per : ∀ (z : ℂ) (a b : ℝ), Circle.exp a = Circle.exp b → h (z,a) = h (z,b))
    (sm : ∀ q ∈ directions, ContDiffAt ℝ ∞ h q) (p : E) (hp : p ∈ domain) :
    ContDiffAt ℝ ∞ (weighted h) p := by
  have db := (diskBarrier_smooth hp.2).comp p (contDiffAt_snd (𝕜 := ℝ))
  by_cases hz : p.2 = 0
  · apply db.congr_of_eventuallyEq
    have ct : Continuous (fun y : E => 4*normSq y.2 - 1) := (continuous_const.mul
      (continuous_normSq.comp continuous_snd)).sub continuous_const
    filter_upwards [ct.continuousAt.eventually_lt_const (show 4*normSq p.2 - 1 < 0 by simp [hz])] with y hy
    simp [weighted,cutoff,Real.smoothTransition.zero_of_nonpos hy.le]
  let branch (v : ℂ) := (v / p.2).arg + p.2.arg
  have mem : (p.1,p.2.arg) ∈ directions := ⟨by simpa using hp.1.le,⟨(neg_pi_lt_arg _).le,arg_le_pi _⟩⟩
  have dlog : ContDiffAt ℝ ∞ Complex.log (p.2 / p.2) := by
    rw [div_self hz]
    exact (Complex.contDiffAt_log Complex.one_mem_slitPlane).restrict_scalars ℝ
  have ddiv : ContDiffAt ℝ ∞ (fun v : ℂ => v / p.2) p.2 := contDiffAt_id.div_const _
  have dbra := (imCLM.contDiff.contDiffAt.comp p.2 (dlog.comp (f := fun v : ℂ => v/p.2) p.2 ddiv)).add (contDiffAt_const (c := p.2.arg))
  have dbr : ContDiffAt ℝ ∞ branch p.2 := by simpa only [branch,Function.comp_apply,Complex.imCLM_apply,Complex.log_im] using dbra
  have same : branch p.2 = p.2.arg := by simp [branch,hz]
  have hs : ContDiffAt ℝ ∞ h (p.1,branch p.2) := by rw [same]; exact sm _ mem
  have reg := hs.comp p (contDiffAt_fst.prodMk (dbr.comp p contDiffAt_snd))
  apply (db.add ((smooth_cutoff.contDiffAt.comp p contDiffAt_snd).mul reg)).congr_of_eventuallyEq
  filter_upwards [continuous_snd.continuousAt.eventually_ne hz] with y hy
  change diskBarrier y.2 + cutoff y.2 * h (y.1,y.2.arg) = diskBarrier y.2 + cutoff y.2 * h (y.1,branch y.2)
  rw [per _ (branch y.2) _ (arg_shift hy hz)]

private theorem principal_polar (p : E) (hp : p.2 ≠ 0) :
    polar (p.1,p.2.arg,Real.log ‖p.2‖) = p := by
  refine Prod.ext rfl ?_
  change Real.exp (Real.log ‖p.2‖) • ConformalFrame.unit p.2.arg = p.2
  rw [Real.exp_log (norm_pos_iff.mpr hp)]
  apply Complex.ext <;> simp [ConformalFrame.unit,Complex.real_smul,-Complex.ofReal_cos,-Complex.ofReal_sin,
    Complex.norm_mul_cos_arg,Complex.norm_mul_sin_arg]

private theorem polar_arg (q : ConformalFrame.Chart) : Circle.exp (polar q).2.arg = Circle.exp q.2.1 := by
  have unit : ConformalFrame.unit q.2.1 = (Circle.exp q.2.1 : ℂ) := by
    apply Complex.ext <;> simp [ConformalFrame.unit,Complex.real_smul,-Complex.ofReal_cos,-Complex.ofReal_sin]
  change Circle.exp (Real.exp q.2.2 • ConformalFrame.unit q.2.1).arg = Circle.exp q.2.1
  rw [Complex.real_smul,Complex.arg_real_mul _ (Real.exp_pos _),unit,Circle.exp_arg]

/-- Every simple conformal disk admits a proper smooth exhaustion of the open
transport bidisk whose actual complex Hessian is strictly positive off a
compact subset. -/
theorem simple_exhaustion {σ : ℂ → ℝ} (simple : SimpleDiskTarget.SimpleMetric σ) :
    ∃ f : E → ℝ, (∀ p ∈ domain, ContDiffAt ℝ ∞ f p) ∧
      (∀ m : ℝ, IsCompact {p ∈ domain | f p ≤ m}) ∧
      ∃ K : Set E, IsCompact K ∧ K ⊆ domain ∧ ∀ p ∈ domain, p ∉ K → StrictAt (J σ) f p := by
  obtain ⟨h,per,good⟩ := exists_periodic_weight simple
  have sm (p) (hp : p ∈ directions) := (good p hp).1
  obtain ⟨η,hη,collar⟩ := PolarCollar.uniform_collar simple.smooth directions_compact
    (fun p hp => (sm p hp).of_le (by decide)) (by
      rw [projected_X]; exact fun p hp => (good p hp).2)
  have e : directions.Nonempty := ⟨(0,0),by simp [directions,Real.pi_pos.le]⟩
  obtain ⟨m,_,hm⟩ := directions_compact.exists_isMaxOn e (f := fun p => |h p|)
    (fun p hp => (sm p hp).continuousAt.abs.continuousWithinAt)
  have gap (p : E) (hp : p ∈ domain) : |weighted h p - diskBarrier p.2| ≤ |h m| := by
    have b := isMaxOn_iff.mp hm (p.1,p.2.arg) (show (p.1,p.2.arg) ∈ directions from
      ⟨by simpa using hp.1.le,⟨(neg_pi_lt_arg _).le,arg_le_pi _⟩⟩)
    rw [weighted,add_sub_cancel_left,abs_mul,cutoff,abs_of_nonneg (Real.smoothTransition.nonneg _)]
    exact (mul_le_of_le_one_left (abs_nonneg _) (Real.smoothTransition.le_one _)).trans b
  let r := max (3/4 : ℝ) (1-η/2)
  have rlt : r < 1 := max_lt (by norm_num) (by linarith)
  have vel (p : E) (hp : p ∈ domain) (hr : r < ‖p.2‖) : StrictAt (J σ) (weighted h) p := by
    have lo : 3/4 < ‖p.2‖ := (le_max_left ..).trans_lt hr
    have hi : 1-η/2 < ‖p.2‖ := (le_max_right ..).trans_lt hr
    have hv : 0 < ‖p.2‖ := by linarith
    let q : ConformalFrame.Chart := (p.1,p.2.arg,Real.log ‖p.2‖)
    have eq : polar q = p := principal_polar p (norm_pos_iff.mp hv)
    have neg : q.2.2 < 0 := Real.log_neg hv hp.2
    have radial : Real.exp (2*q.2.2) = ‖p.2‖^2 := by
      rw [show 2*q.2.2 = q.2.2 + q.2.2 by ring,Real.exp_add,← pow_two,show q.2.2 = Real.log ‖p.2‖ by rfl,Real.exp_log hv]
    have bound : ConformalFrame.t q < η := by
      rw [ConformalFrame.t,ConformalFrame.radialParameter,radial,div_lt_iff₀ (by positivity)]
      nlinarith [sq_nonneg (1-‖p.2‖),mul_nonneg hη.le (sq_nonneg ‖p.2‖)]
    have qmem : PolarCollar.direction q ∈ directions := ⟨by simpa [q] using hp.1.le,⟨(neg_pi_lt_arg _).le,arg_le_pi _⟩⟩
    have df : ContDiffAt ℝ 2 (weighted h) (polar q) := by
      rw [eq]; exact (weighted_smooth per sm p hp).of_le (by decide)
    rw [← eq]
    apply strict_of_polar simple.smooth neg df
    apply StrictAt.congr (collar q qmem neg bound)
    have sq : 1 < 4*normSq (polar q).2 - 1 := by rw [eq,Complex.normSq_eq_norm_sq]; nlinarith [sq_nonneg (‖p.2‖-3/4)]
    have cc : Continuous (fun y : ConformalFrame.Chart => 4*normSq (polar y).2 - 1) :=
      (continuous_const.mul (continuous_normSq.comp (continuous_snd.comp polar_smooth.continuous))).sub continuous_const
    filter_upwards [cc.continuousAt.eventually_const_lt sq,(continuous_snd.comp continuous_snd).continuousAt.eventually_lt_const neg] with y hy hy'
    change FrameLevi.radial (ConformalFrame.t y) + h (PolarCollar.direction y) = _
    rw [polar_barrier hy']
    simp only [Function.comp_apply,weighted,cutoff,Real.smoothTransition.one_of_one_le hy.le,one_mul]
    exact congrArg (_ + ·) (per y.1 _ _ (polar_arg y).symm)
  obtain ⟨L,hL,rb,hrb,hb⟩ := exists_base_radius simple
  obtain ⟨_,g⟩ := logarithmic_collar_exhaustion (J σ) (weighted h) L |h m| rb r hL hrb rlt
    (weighted_smooth per sm) gap (fun _ hp => (J_smooth simple.smooth hp.2).differentiableAt (by simp))
    (fun _ hp => J_sq σ hp.2) vel hb
  exact ⟨_,g⟩

end TransportOkaGrauert.PhysicalStein
