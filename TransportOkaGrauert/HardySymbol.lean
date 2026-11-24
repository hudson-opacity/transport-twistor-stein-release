import TransportOkaGrauert.FourierCollar
import TransportOkaGrauert.ScalarGeneralReduction
import TransportOkaGrauert.PhysicalSteinCollar

/-! # The regularized power functions and their polar representation -/
namespace TransportOkaGrauert.HardySymbol
noncomputable section
open Complex Metric Set Filter AddCircle SmoothFourierFamily FourierCollar
open scoped ContDiff Topology ComplexConjugate

def cutoffExp (s : ℝ) := Real.exp s * Real.smoothTransition (1-s)

theorem cutoff_eq {s : ℝ} (hs : s ≤ 0) : cutoffExp s = Real.exp s := by
  rw [cutoffExp,Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ 1-s),mul_one]

theorem symbol : Symbol cutoffExp := by
  have hs : ContDiff ℝ ∞ cutoffExp := Real.contDiff_exp.mul
    (Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id))
  refine ⟨hs,fun k => ?_⟩
  have H := (contDiff_infty.mp hs k).continuous_iteratedDeriv' k
  obtain ⟨C,hC⟩ := (isCompact_Icc (a := (0:ℝ)) (b := 1)).bddAbove_image H.norm.continuousOn
  refine ⟨max C 1,fun s => ?_⟩
  rcases lt_or_ge s 0 with hn | hn
  · have same : cutoffExp =ᶠ[𝓝 s] Real.exp := by
      filter_upwards [gt_mem_nhds hn] with t ht using cutoff_eq ht.le
    rw [same.iteratedDeriv_eq k,iteratedDeriv_eq_iterate,Real.iter_deriv_exp,Real.norm_eq_abs,Real.abs_exp]
    exact (Real.exp_le_one_iff.mpr hn.le).trans (le_max_right ..)
  · rcases le_or_gt s 1 with hp | hp
    · exact (hC ⟨s,⟨hn,hp⟩,rfl⟩).trans (le_max_left ..)
    · have same : cutoffExp =ᶠ[𝓝 s] (fun _ => 0) := by
        filter_upwards [lt_mem_nhds hp] with t ht
        simp [cutoffExp,Real.smoothTransition.zero_of_nonpos (show 1-t ≤ 0 by linarith)]
      rw [same.iteratedDeriv_eq k,iteratedDeriv_const]
      split <;> simp [zero_le_one.trans (le_max_right C 1)]

local instance : Fact (0 < period) := ⟨Real.two_pi_pos⟩
abbrev Trace := ScalarGeneralTransport.Trace
abbrev Angle := DiskSeries.Angle
abbrev Chart := ConformalFrame.Chart

def a (u : Trace) (n : ℤ) (z : ℂ) := fourierCoeff (fun θ : Angle => u z θ.toCircle) n

theorem coeff_lift (u : Trace) (n : ℤ) (z : ℂ) :
    coeff (ScalarGeneralTransport.lifted u) n z = a u n z := by
  rw [coeff,fourierCoeffOn_eq_integral,a,fourierCoeff_eq_intervalIntegral _ _ 0]
  simp [ScalarGeneralTransport.lifted,ChartModes.toCircle_angle]

def rotated (u : Trace) (p : Chart × ℝ) := u p.1.1 (Circle.exp (p.2+p.1.2.1))

theorem rotated_smooth {u : Trace} (hu : ContDiff ℝ ∞ (ScalarGeneralTransport.lifted u)) :
    ContDiff ℝ ∞ (rotated u) := hu.comp ((contDiff_fst.comp contDiff_fst).prodMk
      (contDiff_snd.add ((contDiff_fst.comp contDiff_snd).comp contDiff_fst)))

theorem rotated_periodic (u : Trace) : PeriodicFamily (rotated u) := by
  intro p t
  simp only [rotated,add_right_comm t period p.2.1]
  exact congrArg (u p.1) (Circle.periodic_exp _)

private theorem shift (f : Angle → ℂ) (y : Angle) (k : ℤ) :
    fourierCoeff (fun x : Angle => f (x+y)) k = fourier k y * fourierCoeff f k := by
  let g (x : Angle) := fourier (-k) x * f x
  have char (x : Angle) : fourier k y * g (x+y) = fourier (-k) x * f (x+y) := by
    have e : (fourier k y : ℂ) * fourier (-k) y = 1 := by
      rw [← fourier_add,add_neg_cancel,fourier_zero]
    simp only [g,fourier_apply,zsmul_add,toCircle_add,Circle.coe_mul] at e ⊢
    linear_combination (((↑((-k) • x).toCircle : ℂ)) * f (x+y)) * e
  unfold fourierCoeff
  simp only [smul_eq_mul]
  rw [← MeasureTheory.integral_const_mul]
  change (∫ x, fourier (-k) x * f (x+y) ∂haarAddCircle) =
    ∫ x, fourier k y * g x ∂haarAddCircle
  calc
    _ = ∫ x, fourier k y * g (x+y) ∂haarAddCircle := by simp_rw [char]
    _ = _ := MeasureTheory.integral_add_right_eq_self (fun x => fourier k y * g x) y

theorem coeff_rotated (u : Trace) (n : ℕ) (p : Chart) :
    coeff (rotated u) (n:ℤ) p = (Circle.exp p.2.1 : ℂ)^n * a u n p.1 := by
  let f (x : Angle) := u p.1 x.toCircle
  let y : Angle := p.2.1
  have eq := shift f y n
  have e : fourier (n:ℤ) y = (Circle.exp p.2.1 : ℂ)^n := by
    simp [fourier_apply,y,AddCircle.toCircle_nsmul,ChartModes.toCircle_angle]
  let v : Trace := fun z w => u z (w * Circle.exp p.2.1)
  have ev : coeff (rotated u) (n:ℤ) p = coeff (ScalarGeneralTransport.lifted v) n p.1 := by
    unfold coeff
    congr 1
    funext t
    simp [rotated,ScalarGeneralTransport.lifted,v,Circle.exp_add]
  rw [ev,coeff_lift,← e]
  simpa only [a,f,y,v,AddCircle.toCircle_add,ChartModes.toCircle_angle] using eq

def modePower (n : ℕ) (w : ℂ) : ℂ :=
  if ‖w‖ ≤ 1 then w^n else cutoffExp (n*Real.log ‖w‖) • (w/(‖w‖:ℂ))^n

def extension (u : Trace) (p : ChartStein.E) :=
  a u 0 p.1 + ∑' n : ℕ, modePower (n+1) p.2 * a u (n+1 : ℕ) p.1

private theorem unit_angle (t : ℝ) : ConformalFrame.unit t = (Circle.exp t : ℂ) := by
  apply Complex.ext <;> simp [ConformalFrame.unit,Circle.coe_exp,Complex.real_smul,-Complex.ofReal_cos,-Complex.ofReal_sin]

private theorem power_polar (p : Chart) (n : ℕ) : modePower n (PolarCR.polar p).2 =
    cutoffExp (n*p.2.2) • (Circle.exp p.2.1 : ℂ)^n := by
  rw [modePower,PhysicalStein.polar_norm]
  have e : (PolarCR.polar p).2 = Real.exp p.2.2 • (Circle.exp p.2.1 : ℂ) := by
    simp [PolarCR.polar,unit_angle]
  rw [e]
  split_ifs with h
  · rw [cutoff_eq (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (Real.exp_le_one_iff.mp h)),
      Real.exp_nat_mul,Complex.real_smul,mul_pow,Complex.real_smul,Complex.ofReal_pow]
  · simp [Real.log_exp,Complex.real_smul]

theorem smooth_polar {u : Trace} (hu : ContDiff ℝ ∞ (ScalarGeneralTransport.lifted u)) :
    ContDiff ℝ ∞ (extension u ∘ PolarCR.polar) := by
  let l : Chart →L[ℝ] ℝ := (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℂ (ℝ × ℝ))
  have S := FourierCollar.smooth (rotated_smooth hu) (rotated_periodic u) symbol l 0
  have eq : extension u ∘ PolarCR.polar = fun p : Chart =>
      coeff (ScalarGeneralTransport.lifted u) 0 p.1 + series (rotated u) cutoffExp l 0 p := by
    funext p
    simp only [Function.comp_apply,extension,coeff_lift,series]
    congr 1
    apply tsum_congr
    intro n
    rw [power_polar]
    change _ = (((n+1 : ℕ):ℝ)^0*cutoffExp (((n+1 : ℕ):ℝ)*l p)) • coeff (rotated u) (n+1 : ℕ) p
    rw [coeff_rotated]
    simp [l,PolarCR.polar,Complex.real_smul,mul_assoc]
  rw [eq]
  exact ((coeff_smooth hu 0).comp contDiff_fst).add S

theorem smooth_off_zero {u : Trace} (hu : ContDiff ℝ ∞ (ScalarGeneralTransport.lifted u))
    {p : ChartStein.E} (hp : p.2 ≠ 0) : ContDiffAt ℝ ∞ (extension u) p := by
  obtain ⟨q,hq,_⟩ := PhysicalStein.polar_covers hp
  rw [← hq]
  let L := fderiv ℝ PolarCR.polar q
  have inj : Function.Injective L := by
    intro x y h
    have hz : L (x-y) = 0 := by rw [map_sub,h,sub_self]
    rw [show L = fderiv ℝ PolarCR.polar q from rfl,PolarCR.polar_derivative] at hz
    have h1 := congrArg Prod.fst hz
    have h2 := congrArg Prod.snd hz
    have hw : (PolarCR.polar q).2 ≠ 0 := norm_ne_zero_iff.mp ((PhysicalStein.polar_norm q).trans_ne (Real.exp_ne_zero _))
    change (PolarCR.polar q).2 * (((x-y).2.2 : ℂ)+I*(x-y).2.1) = 0 at h2
    have h3 := (mul_eq_zero.mp h2).resolve_left hw
    have hr := congrArg Complex.re h3
    have hi := congrArg Complex.im h3
    apply sub_eq_zero.mp
    exact Prod.ext h1 (Prod.ext (by simpa using hi) (by simpa using hr))
  let e := ContinuousLinearEquiv.ofBijective L (LinearMap.ker_eq_bot.mpr inj)
    (LinearMap.range_eq_top.mpr (PhysicalStein.polar_submersion q))
  have D : HasFDerivAt PolarCR.polar e.toContinuousLinearMap q :=
    (PhysicalStein.polar_smooth.differentiable (by simp) q).hasFDerivAt
  have sm : ContDiffAt ℝ ∞ PolarCR.polar q := PhysicalStein.polar_smooth.contDiffAt
  have hi := sm.to_localInverse D (by simp)
  have hi0 := sm.localInverse_apply_image D (by simp)
  have eq := (sm.hasStrictFDerivAt' D (by simp)).eventually_right_inverse
  have atQ : ContDiffAt ℝ ∞ (extension u ∘ PolarCR.polar) (sm.localInverse D (by simp) (PolarCR.polar q)) := by rw [hi0]; exact (smooth_polar hu).contDiffAt
  have H := atQ.comp (PolarCR.polar q) hi
  apply H.congr_of_eventuallyEq
  filter_upwards [eq] with y hy
  exact congrArg (extension u) hy.symm

end
end TransportOkaGrauert.HardySymbol
