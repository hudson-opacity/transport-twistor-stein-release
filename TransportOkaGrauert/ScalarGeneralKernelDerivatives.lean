import TransportOkaGrauert.ScalarGeneralKernelRemainder

/-! # First spatial derivative of the curved kernel remainder

Holding the displacement fixed gives the derivatives under simultaneous
translation of source and target. They have a bounded radial representation
at every order. One more differentiation in the displacement costs at most
the inverse separation. -/

noncomputable section
namespace TransportOkaGrauert.ScalarGeneralKernel
open Metric Set Filter Complex
open scoped ContDiff Topology

private def direction (z : ℂ) := ‖z‖⁻¹ • z

private theorem scale_direction (z : ℂ) : ‖z‖ • direction z = z := by
  by_cases h : z = 0
  · simp [h]
  · rw [direction,smul_inv_smul₀ (norm_ne_zero_iff.mpr h)]

private theorem direction_bound (z : ℂ) : ‖direction z‖ ≤ 1 := by
  by_cases h : z = 0
  · simp [direction,h]
  · simp [direction,norm_ne_zero_iff.mpr h]

private theorem direction_lip (w z : ℂ) (hz : z ≠ 0) :
    ‖direction w - direction z‖ ≤ 2 / ‖z‖ * ‖w-z‖ := by
  have hp := norm_pos_iff.mpr hz
  have e : ‖z‖ • (direction w-direction z) = (‖z‖-‖w‖) • direction w + (w-z) := by
    rw [smul_sub,sub_smul,scale_direction,scale_direction]; abel
  have bound := norm_add_le ((‖z‖-‖w‖) • direction w) (w-z)
  rw [← e,norm_smul,Real.norm_of_nonneg (norm_nonneg _),norm_smul,Real.norm_eq_abs] at bound
  have d := abs_norm_sub_norm_le z w
  rw [norm_sub_rev z w] at d
  have e' := mul_le_mul_of_nonneg_left (direction_bound w) (abs_nonneg (‖z‖-‖w‖))
  rw [mul_one] at e'
  apply (le_of_mul_le_mul_left (a := ‖z‖) _ hp)
  rw [← mul_assoc, show ‖z‖ * (2/‖z‖) = 2 by field_simp]
  linarith

private def radial (a w : ℂ) : RadialParameter := ((a,‖w‖),direction w)

private theorem radial_derivative_bound (a z : ℂ) (hz : z ≠ 0) :
    ‖fderiv ℝ (radial a) z‖ ≤ 1+2/‖z‖ := by
  apply norm_fderiv_le_of_lip' ℝ (by positivity)
  apply Eventually.of_forall
  intro w
  have l := direction_lip w z hz
  have n := abs_norm_sub_norm_le w z
  have p : 0 ≤ (2/‖z‖) * ‖w-z‖ := by positivity
  change max (max ‖a-a‖ ‖‖w‖-‖z‖‖) ‖direction w - direction z‖ ≤ _
  rw [sub_self,norm_zero,Real.norm_eq_abs,show max 0 |‖w‖-‖z‖| = |‖w‖-‖z‖| from max_eq_right (abs_nonneg _),add_mul,one_mul]
  exact max_le (by linarith) (by linarith [norm_nonneg (w-z)])

private theorem radial_differentiable (a z : ℂ) (hz : z ≠ 0) : DifferentiableAt ℝ (radial a) z := by
  have n := (contDiffAt_norm (n := (∞ : WithTop ℕ∞)) ℝ hz).differentiableAt (by simp)
  exact ((differentiableAt_const a).prodMk n).prodMk ((n.inv (norm_ne_zero_iff.mpr hz)).smul differentiableAt_id)

private def baseLinear : ℂ →L[ℝ] RadialParameter := ((ContinuousLinearMap.id ℝ ℂ).prod 0).prod 0

/-- Ambient smooth field encoding the m-th derivative in the centre when
the separation vector is held fixed. -/
def centreJet (m : ℕ) (R : RadialParameter → ℝ) (p : RadialParameter) :=
  (iteratedFDeriv ℝ m R p).compContinuousLinearMap (fun _ => baseLinear)

theorem centreJet_smooth {R : RadialParameter → ℝ} (sR : ContDiff ℝ ∞ R) (m : ℕ) :
    ContDiff ℝ ∞ (centreJet m R) :=
  (ContinuousMultilinearMap.compContinuousLinearMapL (G := ℝ) (fun _ : Fin m => baseLinear)).contDiff.comp
    (sR.iteratedFDeriv_right (m := ∞) (i := m) (by exact WithTop.coe_le_coe.mpr le_top))

theorem centreJet_eq {R : RadialParameter → ℝ} (sR : ContDiff ℝ ∞ R) (m : ℕ) (a : ℂ) (r : ℝ) (v : ℂ) :
    centreJet m R ((a,r),v) = iteratedFDeriv ℝ m (fun b : ℂ => R ((b,r),v)) a := by
  let c : RadialParameter := ((0,r),v)
  let shift (q : RadialParameter) := R (q+c)
  have ss : ContDiff ℝ ∞ shift := sR.comp (contDiff_id.add contDiff_const)
  have eq : (fun b : ℂ => R ((b,r),v)) = shift ∘ baseLinear := by
    funext b
    simp [shift,c,baseLinear]
  rw [eq,baseLinear.iteratedFDeriv_comp_right ss a (by exact_mod_cast le_top)]
  change _ = (iteratedFDeriv ℝ m (fun q => R (q+c)) (baseLinear a)).compContinuousLinearMap _
  rw [iteratedFDeriv_comp_add_right]
  simp [centreJet,baseLinear,c]

/-- Uniform control of simultaneous translations, and of one spatial
derivative following any number of such translations. -/
theorem spatial_derivative_bounds {K : Set ℂ} (compact : IsCompact K) {δ : ℝ} (hδ : 0 < δ)
    {R : RadialParameter → ℝ} (sR : ContDiff ℝ ∞ R) (m : ℕ) :
    ∃ M : ℝ, 0 < M ∧ ∀ a ∈ K, ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ ≤ δ →
      ‖iteratedFDeriv ℝ m (fun b : ℂ => R ((b,‖z‖),‖z‖⁻¹ • z)) a‖ ≤ M ∧
      ‖fderiv ℝ (fun w : ℂ => iteratedFDeriv ℝ m (fun b : ℂ => R ((b,‖w‖),‖w‖⁻¹ • w)) a) z‖ ≤ M / ‖z‖ := by
  let G := centreJet m R
  have sG : ContDiff ℝ ∞ G := centreJet_smooth sR m
  let T : Set RadialParameter := (K ×ˢ Icc 0 δ) ×ˢ sphere (0:ℂ) 1
  have hT : IsCompact T := (compact.prod isCompact_Icc).prod (isCompact_sphere _ _)
  obtain ⟨M₀,b₀⟩ := hT.bddAbove_image sG.continuous.norm.continuousOn
  obtain ⟨M₁,b₁⟩ := hT.bddAbove_image (sG.fderiv_right (m := ∞) (by simp)).continuous.norm.continuousOn
  let M := 1 + |M₀| + |M₁| *(δ+2)
  have pos : 0 < M := by dsimp [M]; positivity
  refine ⟨M,pos,?_⟩
  intro a ha z hz small
  have mem : radial a z ∈ T := ⟨⟨ha,hz.le,small⟩,mem_sphere_zero_iff_norm.mpr (by simp [radial,direction,hz.ne'])⟩
  have bound := b₁ ⟨radial a z,mem,rfl⟩
  have eq (w : ℂ) : iteratedFDeriv ℝ m (fun b : ℂ => R ((b,‖w‖),‖w‖⁻¹ • w)) a = G (radial a w) :=
    (centreJet_eq sR m a _ _).symm
  simp_rw [eq]
  constructor
  · have h := b₀ ⟨radial a z,mem,rfl⟩
    change ‖G (radial a z)‖ ≤ M₀ at h
    exact h.trans ((le_abs_self _).trans (by dsimp [M]; nlinarith [abs_nonneg M₁]))
  · change ‖fderiv ℝ (G ∘ radial a) z‖ ≤ _
    rw [fderiv_comp z (sG.differentiable (by simp) _) (radial_differentiable a z (norm_pos_iff.mp hz))]
    apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
    have est := mul_le_mul (le_trans bound (le_abs_self M₁)) (radial_derivative_bound a z (norm_pos_iff.mp hz))
      (norm_nonneg _) (abs_nonneg _)
    apply est.trans
    apply (le_div_iff₀ hz).mpr
    have iden : |M₁| * (1+2/‖z‖) * ‖z‖ = |M₁| * (‖z‖+2) := by field_simp
    rw [iden]
    dsimp [M]
    nlinarith [mul_nonneg (abs_nonneg M₁) (sub_nonneg.mpr small),abs_nonneg M₀]

end TransportOkaGrauert.ScalarGeneralKernel
