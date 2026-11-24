import TransportOkaGrauert.HardySymbol

/-! # A jointly smooth disk lift of the positive-frequency projection
The regularized series is smooth across the unit circle. The usual Cauchy
kernel supplies its smooth Cartesian representation near zero velocity. -/
namespace TransportOkaGrauert.HardyDisk
noncomputable section
open Complex Metric Set Filter AddCircle MeasureTheory SmoothFourierFamily HardySymbol
open scoped ContDiff Topology ComplexConjugate
local instance : Fact (0 < period) := ⟨Real.two_pi_pos⟩
private abbrev Alg := C(Angle,ℂ)

private def circleProfile {u : Trace} (hu : ContDiff ℝ ∞ (ScalarGeneralTransport.lifted u)) (z : ℂ) : Alg where
  toFun θ := u z θ.toCircle
  continuous_toFun := by
    apply continuous_coinduced_dom.mpr
    change Continuous (fun t : ℝ => u z (AddCircle.toCircle (t:Angle)))
    simp only [ChartModes.toCircle_angle]
    exact hu.continuous.comp (continuous_const.prodMk continuous_id)

private theorem summable_coeff {u : Trace} (hu : ContDiff ℝ ∞ (ScalarGeneralTransport.lifted u)) (z : ℂ) :
    Summable fun n : ℕ => ‖a u n z‖ := by
  apply Summable.comp_injective (f := fun n : ℤ => ‖a u n z‖) _ Nat.cast_injective
  apply FourierDecay.summable_fourierCoeff_norm
  simp only [ChartModes.toCircle_angle]
  exact (hu.comp (contDiff_const.prodMk contDiff_id)).of_le (by decide)

private def average : Alg →L[ℂ] ℂ :=
  (L1.integralCLM' ℂ).comp (ContinuousMap.toLp 1 haarAddCircle ℂ)

private theorem average_apply (f : Alg) : average f = ∫ θ, f θ ∂haarAddCircle := by
  unfold average
  rw [ContinuousLinearMap.comp_apply,← L1.integral_eq',L1.integral_eq_integral]
  exact integral_congr_ae (ContinuousMap.coeFn_toLp haarAddCircle f)

private def moment (k : ℤ) : Alg →L[ℂ] ℂ :=
  average.comp (ContinuousLinearMap.mul ℂ Alg (fourier (-k)))

private theorem moment_apply (k : ℤ) (f : Alg) : moment k f = fourierCoeff f k := by
  rw [moment,ContinuousLinearMap.comp_apply,average_apply]
  rfl

private theorem char_nat (n : ℕ) (θ : Angle) : fourier (n:ℤ) θ = (θ.toCircle : ℂ)^n := by
  simp [fourier_apply,AddCircle.toCircle_nsmul]

private theorem char_neg (n : ℕ) (θ : Angle) : fourier (-(n:ℤ)) θ = (fourier (-1) θ)^n := by
  rw [fourier_neg, char_nat, fourier_neg (n := (1:ℤ)), fourier_one, map_pow]

private theorem interior_series {u : Trace} (hu : ContDiff ℝ ∞ (ScalarGeneralTransport.lifted u))
    (z w : ℂ) (hw : ‖w‖ ≤ 1) :
    extension u (z,w) = ∑' n : ℕ, w^n*a u n z := by
  have sm : Summable (fun n : ℕ => w^n*a u n z) :=
    (summable_coeff hu z).of_norm_bounded fun n => by rw [norm_mul,norm_pow]; exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg w) hw)
  rw [sm.tsum_eq_zero_add]
  simp [extension,modePower,hw]

theorem fibres {u : Trace} (hu : ContDiff ℝ ∞ (ScalarGeneralTransport.lifted u)) (z : ℂ) :
    DifferentiableOn ℂ (fun w => extension u (z,w)) (ball 0 1) := by
  apply DifferentiableOn.congr _ (fun w hw => interior_series hu z w (mem_ball_zero_iff.mp hw).le)
  exact differentiableOn_tsum_of_summable_norm (summable_coeff hu z)
    (fun n => ((differentiable_id.pow n).mul_const (a u n z)).differentiableOn) isOpen_ball
    (fun n w hw => by rw [norm_mul,norm_pow]; exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) (mem_ball_zero_iff.mp hw).le))

theorem moments {u : Trace} (hu : ContDiff ℝ ∞ (ScalarGeneralTransport.lifted u)) (z : ℂ) (k : ℤ) :
    fourierCoeff (fun θ : Angle => extension u (z,(θ.toCircle:ℂ))) k = if 0 ≤ k then a u k z else 0 := by
  let F (n : ℕ) : Alg := a u n z • fourier (n:ℤ)
  have sm : Summable F := (summable_coeff hu z).of_norm_bounded fun n => by
    simp [F,norm_smul,fourier_norm]
  have eq : (fun θ : Angle => extension u (z,(θ.toCircle:ℂ))) = (∑' n, F n : Alg) := by
    funext θ
    rw [interior_series hu z _ (Circle.norm_coe θ.toCircle).le]
    let ev : Alg →L[ℂ] ℂ := ContinuousMap.evalCLM ℂ θ
    change _ = ev (∑' n, F n)
    rw [ev.map_tsum sm]
    apply tsum_congr
    intro n
    change _ = a u n z * fourier (n:ℤ) θ
    rw [char_nat,mul_comm]
  rw [eq,← moment_apply,(moment k).map_tsum sm]
  have ck (n : ℕ) : moment k (F n) = if (n:ℤ) = k then a u n z else 0 := by
    change moment k (a u n z • fourier (n:ℤ)) = _
    rw [map_smul,moment_apply, fourierCoeff_fourier]
    by_cases h : (n:ℤ) = k <;> simp [h,Pi.single_apply]
  simp_rw [ck]
  split_ifs with hk
  · lift k to ℕ using hk
    simpa only [Nat.cast_inj] using (tsum_ite_eq k (fun n : ℕ => a u n z))
  · simp [show ∀ n : ℕ, (n:ℤ) ≠ k by omega]

private theorem cauchy {u : Trace} (hu : ContDiff ℝ ∞ (ScalarGeneralTransport.lifted u))
    (z w : ℂ) (hw : ‖w‖ < 1) : extension u (z,w) =
      fourierCoeff (fun θ : Angle => u z θ.toCircle * (1-w*fourier (-1) θ)⁻¹) 0 := by
  let Q : Alg := w • fourier (-1)
  let f := circleProfile hu z
  have small : ‖Q‖ < 1 := by simpa [Q,norm_smul,fourier_norm] using hw
  have sm := summable_geometric_of_norm_lt_one small
  let A := average.comp (ContinuousLinearMap.mul ℂ Alg f)
  have aq (n : ℕ) : A (Q^n) = w^n * a u n z := by
    change average (f*Q^n) = _
    have eq : f*Q^n = w^n • (fourier (-(n:ℤ)) * f) := by
      ext θ
      change f θ * (w*fourier (-1) θ)^n = w^n*(fourier (-(n:ℤ)) θ*f θ)
      rw [char_neg,mul_pow]
      ring
    rw [eq,map_smul,average_apply]
    rfl
  have ev (θ : Angle) : (∑' n : ℕ, Q^n) θ = (1-w*fourier (-1) θ)⁻¹ := by
    let L : Alg →L[ℂ] ℂ := ContinuousMap.evalCLM ℂ θ
    rw [show (∑' n : ℕ, Q^n) θ = L (∑' n : ℕ, Q^n) from rfl,L.map_tsum sm]
    change (∑' n : ℕ, (w * fourier (-1) θ)^n) = _
    apply tsum_geometric_of_norm_lt_one
    simpa only [norm_mul,show ‖fourier (-1) θ‖ = 1 from Circle.norm_coe _,mul_one] using hw
  rw [interior_series hu z w hw.le,← funext aq,← A.map_tsum sm]
  change average (f*(∑' n : ℕ, Q^n)) = _
  rw [average_apply,fourierCoeff]
  simp [f,circleProfile,ev]

private def bump : ContDiffBump (0:ℂ) := ⟨1/4,1/2,by norm_num,by norm_num⟩
private def smallW (w : ℂ) := bump w • w
private theorem smallW_lt (w : ℂ) : ‖smallW w‖ < 1 := by
  by_cases h : ‖w‖ < 1/2
  · rw [smallW,norm_smul,Real.norm_eq_abs,abs_of_nonneg bump.nonneg]
    exact (mul_le_of_le_one_left (norm_nonneg _) bump.le_one).trans_lt (lt_trans h (by norm_num))
  · simp [smallW,bump.zero_of_le_dist (x := w) (by simpa [bump,dist_zero_right] using le_of_not_gt h)]

theorem smooth {u : Trace} (hu : ContDiff ℝ ∞ (ScalarGeneralTransport.lifted u)) :
    ContDiff ℝ ∞ (extension u) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  by_cases h : p.2 = 0
  · let F (x : ChartStein.E × ℝ) :=
      u x.1.1 (Circle.exp x.2) * (1-smallW x.1.2*conj (Circle.exp x.2 : ℂ))⁻¹
    have ew : ContDiff ℝ ∞ (fun x : ChartStein.E × ℝ => (Circle.exp x.2 : ℂ)) := by
      simp only [Circle.coe_exp]
      exact ((Complex.ofRealCLM.contDiff.comp contDiff_snd).mul contDiff_const).cexp
    have sw : ContDiff ℝ ∞ smallW := bump.contDiff.smul contDiff_id
    have ne (x : ChartStein.E × ℝ) : (1:ℂ)-smallW x.1.2*conj (Circle.exp x.2 : ℂ) ≠ 0 := by
      apply sub_ne_zero.mpr
      intro e
      have q := congrArg norm e
      simp at q
      linarith [smallW_lt x.1.2]
    have sf : ContDiff ℝ ∞ F := (hu.comp ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd)).mul
      ((contDiff_const.sub ((sw.comp (contDiff_snd.comp contDiff_fst)).mul (Complex.conjCLE.contDiff.comp ew))).inv ne)
    apply (coeff_smooth sf 0).contDiffAt.congr_of_eventuallyEq
    have near : ∀ᶠ y : ChartStein.E in 𝓝 p, ‖y.2‖ < 1/4 :=
      continuous_snd.norm.continuousAt.eventually_lt_const (by change ‖p.2‖ < 1/4; rw [h,norm_zero]; norm_num)
    filter_upwards [near] with y hy'
    have es : smallW y.2 = y.2 := by rw [smallW,bump.one_of_mem_closedBall (mem_closedBall_zero_iff.mpr hy'.le),one_smul]
    rw [cauchy hu _ _ (lt_trans hy' (by norm_num)),coeff,fourierCoeffOn_eq_integral,fourierCoeff_eq_intervalIntegral _ _ 0]
    have negOne (t : ℝ) : fourier (-1) (t:Angle) = conj (Circle.exp t : ℂ) := by
      rw [fourier_neg (n := (1:ℤ)),fourier_one,ChartModes.toCircle_angle]
    simp only [zero_add, sub_zero, neg_zero, fourier_zero, one_smul,negOne,F,es,ChartModes.toCircle_angle]
  · exact smooth_off_zero hu h

theorem projector : ScalarGeneralReduction.HardyProjector := by
  intro u hu
  exact ⟨⟨extension u,smooth hu,fun z _ => fibres hu z⟩,fun z _ k => moments hu z k⟩

end
end TransportOkaGrauert.HardyDisk
