import TransportOkaGrauert.ChartCoefficients

/-! Every angular coefficient of a chart-smooth boundary field is smooth in
the base up to its boundary. Integration has fixed compact angular support. -/

noncomputable section
namespace TransportOkaGrauert.SmoothCoefficient

open SimpleDiskTarget ChartModes CoefficientIntegral Set Filter Metric
open scoped ContDiff Topology
local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

private theorem local_derivative {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (g : ℂ × ℝ → E) (z : ℂ) {T : ℝ} (hT : 0 < T)
    (hg : ∀ t ∈ Icc 0 T, ContDiffAt ℝ ∞ g (z,t)) :
    ∃ u ∈ 𝓝 z, ∀ y ∈ u, HasFDerivAt (fun x => ∫ t in (0 : ℝ)..T, g (x,t))
      (∫ t in (0 : ℝ)..T, baseDerivative g (y,t)) y := by
  let good := {p : ℂ × ℝ | ContDiffAt ℝ 1 g p}
  have ho : IsOpen good := isOpen_iff_mem_nhds.mpr fun p hp =>
    (show ContDiffAt ℝ 1 g p from hp).eventually (by decide)
  have hin : ({z} : Set ℂ) ×ˢ Icc 0 T ⊆ good := by
    rintro ⟨x,t⟩ ⟨rfl, ht⟩
    exact (hg t ht).of_le (show 1 ≤ (∞ : WithTop ℕ∞) by decide)
  obtain ⟨u,v,hu,_,hzu,hv,hsub⟩ := generalized_tube_lemma isCompact_singleton isCompact_Icc ho hin
  refine ⟨u, hu.mem_nhds (hzu (mem_singleton z)), ?_⟩
  intro y hy
  have hgood (t : ℝ) (ht : t ∈ Icc 0 T) : ContDiffAt ℝ 1 g (y,t) := hsub ⟨hy,hv ht⟩
  have he (t : ℝ) (ht : t ∈ uIcc 0 T) : baseDerivative g (y,t) = fderiv ℝ (fun p => g (p,t)) y :=
    (slice_hasFDeriv (hgood t ((uIcc_of_le hT.le) ▸ ht))).fderiv.symm
  rw [intervalIntegral.integral_congr he]
  exact (interval_derivative g y hT hgood).1

private theorem smooth_order (m : ℕ) : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (g : ℂ × ℝ → E) (z : ℂ) {T : ℝ}, 0 < T →
    (∀ t ∈ Icc 0 T, ContDiffAt ℝ ∞ g (z,t)) →
    ContDiffAt ℝ m (fun x => ∫ t in (0 : ℝ)..T, g (x,t)) z := by
  induction m with
  | zero =>
    intro E _ _ _ g z T hT hg
    obtain ⟨u,hu,hd⟩ := local_derivative g z hT hg
    apply contDiffAt_zero.mpr
    exact ⟨u,hu, fun y hy => (hd y hy).continuousAt.continuousWithinAt⟩
  | succ m ih =>
    intro E _ _ _ g z T hT hg
    apply contDiffAt_succ_iff_hasFDerivAt.mpr
    refine ⟨fun y => ∫ t in (0 : ℝ)..T, baseDerivative g (y,t), local_derivative g z hT hg, ?_⟩
    apply ih (ℂ →L[ℝ] E) (baseDerivative g) z hT
    intro t ht
    exact ((hg t ht).fderiv_right (m := ∞) (by simp)).clm_comp contDiffAt_const

/-- Integration over an angular period preserves all orders of base
regularity, allowing the base point to lie on the closed-disk boundary. -/
theorem smooth_integral {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (g : ℂ × ℝ → E) (z : ℂ) {T : ℝ} (hT : 0 < T)
    (hg : ∀ t ∈ Icc 0 T, ContDiffAt ℝ ∞ g (z,t)) :
    ContDiffAt ℝ ∞ (fun x => ∫ t in (0 : ℝ)..T, g (x,t)) z :=
  contDiffAt_infty.mpr fun m => smooth_order m E g z hT hg

/-- Smoothness of each entry of every genuine normalized Haar mode. -/
theorem smooth_mode {n : ℕ} {F : Field n} (hF : SmoothToBoundary F)
    {z : ℂ} (hz : z ∈ closedBall 0 1) (k : ℤ) (i j : Fin n) :
    ContDiffAt ℝ ∞ (fun y => SkewReduction.modeMatrix F y k i j) z := by
  let g (p : ℂ × ℝ) := fourier (-k) (p.2 : DiskSeries.Angle) * F p.1 (Circle.exp p.2) i j
  have hg (t : ℝ) : ContDiffAt ℝ ∞ g (z,t) := by
    apply ContDiffAt.mul _ (hF z hz t i j)
    simp only [fourier_coe_apply]
    simp only [div_eq_mul_inv]
    exact ((contDiffAt_const.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp _ contDiffAt_snd)).mul contDiffAt_const).cexp
  have he : (fun y => SkewReduction.modeMatrix F y k i j) =
      fun y => (1 / (2 * Real.pi) : ℝ) • ∫ t in (0 : ℝ)..2*Real.pi, g (y,t) := by
    funext y
    unfold SkewReduction.modeMatrix
    rw [fourierCoeff_eq_intervalIntegral _ _ 0, zero_add]
    simp only [g, smul_eq_mul, toCircle_angle]
  rw [he]
  exact (smooth_integral g z Real.two_pi_pos (fun t _ => hg t)).const_smul _

end TransportOkaGrauert.SmoothCoefficient
