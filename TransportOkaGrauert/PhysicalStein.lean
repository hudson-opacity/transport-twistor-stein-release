import TransportOkaGrauert.PolarCR
import TransportOkaGrauert.CRCoordinates
import TransportOkaGrauert.CollarGluing

/-! # The transport complex structure in physical disk coordinates

The horizontal covector `dz - μ² d(conj z)` has no singularity at zero velocity.
The vertical covector acquires exactly half the connection coefficient in its
antiholomorphic base component. Together they give a smooth real coframe
whose rows obey the two defining transport CR equations.
-/

noncomputable section
namespace TransportOkaGrauert.PhysicalStein

open Complex ChartStein
open scoped ContDiff ComplexConjugate Topology

private abbrev base : E →L[ℝ] ℂ := .fst ℝ ℂ ℂ
private abbrev fiber : E →L[ℝ] ℂ := .snd ℝ ℂ ℂ
private abbrev anti : E →L[ℝ] ℂ := conjCLE.toContinuousLinearMap.comp base

def horizontal (p : E) : E →L[ℝ] ℂ := base - p.2 ^ 2 • anti

def vertical (σ : ℂ → ℝ) (p : E) : E →L[ℝ] ℂ :=
  fiber + (connectionCoefficient σ p / 2) • anti

def coframe (σ : ℂ → ℝ) (p : E) : E →L[ℝ] E := (horizontal p).prod (vertical σ p)

theorem coframe_apply (σ : ℂ → ℝ) (p w : E) :
    coframe σ p w = (w.1 - p.2^2 * conj w.1, w.2 + (connectionCoefficient σ p / 2) * conj w.1) := rfl

theorem rows_CR (σ : ℂ → ℝ) (p : E) :
    SatisfiesCR σ p (horizontal p) ∧ SatisfiesCR σ p (vertical σ p) := by
  have sq := Complex.I_sq
  constructor <;> constructor <;> simp [horizontal, vertical, smul_eq_mul] <;> grind only

theorem coframe_bijective (σ : ℂ → ℝ) {p : E} (h : ‖p.2‖ < 1) :
    Function.Bijective (coframe σ p) := by
  have hi : Function.Injective (coframe σ p) := by
    apply LinearMap.ker_eq_bot.mp (show LinearMap.ker (coframe σ p).toLinearMap = ⊥ from ?_)
    apply LinearMap.ker_eq_bot'.mpr
    intro v hv
    have hb : FlatScalar.firstIntegral v.1 p.2 = 0 := congrArg Prod.fst hv
    have hz := (SteinDivisor.firstIntegral_interior_zero_iff _ _ h).mp hb
    exact Prod.ext hz (by simpa [coframe_apply, hz] using congrArg Prod.snd hv)
  exact ⟨hi, LinearMap.injective_iff_surjective.mp (show Function.Injective (coframe σ p).toLinearMap from hi)⟩

def J (σ : ℂ → ℝ) (p : E) : E →L[ℝ] E :=
  (coframe σ p).inverse.comp (I • coframe σ p)

theorem coframe_J (σ : ℂ → ℝ) {p : E} (hp : ‖p.2‖ < 1) (v : E) :
    coframe σ p (J σ p v) = I • coframe σ p v := by
  have hb := coframe_bijective σ hp
  let e := ContinuousLinearEquiv.ofBijective (coframe σ p)
    (LinearMap.ker_eq_bot.mpr hb.1) (LinearMap.range_eq_top.mpr hb.2)
  change e ((e : E →L[ℝ] E).inverse (I • coframe σ p v)) = _
  simp

theorem J_sq (σ : ℂ → ℝ) {p : E} (hp : ‖p.2‖ < 1) (v : E) :
    J σ p (J σ p v) = -v := by
  apply (coframe_bijective σ hp).1
  simp only [coframe_J σ hp, smul_smul, I_mul_I, neg_one_smul, map_neg]

theorem J_zero (σ : ℂ → ℝ) (z : ℂ) (v : E) : J σ (z,0) v = I • v := by
  have eq (w : E) : coframe σ (z,0) w = w := by
    simp [coframe_apply, connectionCoefficient]
  simpa only [eq] using coframe_J σ (p := (z,0)) (by simp) v

theorem coframe_smooth {σ : ℂ → ℝ} (hs : ContDiff ℝ ∞ σ) : ContDiff ℝ ∞ (coframe σ) := by
  have ds := (hs.fderiv_right (m := ∞) (by simp)).comp (contDiff_fst (E := ℂ) (F := ℂ))
  have sx := ofRealCLM.contDiff.comp (ds.clm_apply (contDiff_const (c := (1 : ℂ))))
  have sy := ofRealCLM.contDiff.comp (ds.clm_apply (contDiff_const (c := I)))
  have hc : ContDiff ℝ ∞ (connectionCoefficient σ) := by
    apply contDiff_snd.mul
    exact ((contDiff_snd.pow 2).mul (sx.sub (contDiff_const.mul sy))).sub
      (sx.add (contDiff_const.mul sy))
  have dh : ContDiff ℝ ∞ horizontal := contDiff_const.sub ((contDiff_snd.pow 2).smul contDiff_const)
  have dv : ContDiff ℝ ∞ (vertical σ) := contDiff_const.add ((hc.div_const _).smul contDiff_const)
  have eq : coframe σ = fun p =>
      (ContinuousLinearMap.inl ℝ ℂ ℂ).comp (horizontal p) +
        (ContinuousLinearMap.inr ℝ ℂ ℂ).comp (vertical σ p) := by
    funext p
    apply ContinuousLinearMap.ext
    intro w
    simp [coframe]
  rw [eq]
  exact (contDiff_const.clm_comp dh).add (contDiff_const.clm_comp dv)

theorem J_smooth {σ : ℂ → ℝ} (hs : ContDiff ℝ ∞ σ) {p : E} (hp : ‖p.2‖ < 1) :
    ContDiffAt ℝ ∞ (J σ) p := by
  have hb := coframe_bijective σ hp
  have hi : (coframe σ p).IsInvertible := ⟨ContinuousLinearEquiv.ofBijective (coframe σ p)
    (LinearMap.ker_eq_bot.mpr hb.1) (LinearMap.range_eq_top.mpr hb.2), rfl⟩
  have dc := (coframe_smooth hs).contDiffAt (x := p)
  exact (hi.contDiffAt_map_inverse.comp p dc).clm_comp ((contDiffAt_const (c := I)).smul dc)

private def complexify (D : E →L[ℝ] ℂ) (h : ∀ v, D (I • v) = I * D v) : E →L[ℂ] ℂ where
  toFun := D
  map_add' := D.map_add
  map_smul' a v := by
    have eq : a • v = a.re • v + a.im • (I • v) := by
      conv_lhs => rw [← Complex.re_add_im a]
      rw [add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul]
    rw [eq, map_add, map_smul, map_smul, h]
    change (a.re:ℂ) * D v + (a.im:ℂ) * (I * D v) = a * D v
    conv_rhs => rw [← Complex.re_add_im a]
    ring
  cont := D.continuous

/-- The physical `J` has precisely the CR covectors specified in the Stein target. -/
theorem satisfiesCR_iff (σ : ℂ → ℝ) {p : E} (hp : ‖p.2‖ < 1) (D : E →L[ℝ] ℂ) :
    SatisfiesCR σ p D ↔ ∀ v, D (J σ p v) = I * D v := by
  have hb := coframe_bijective σ hp
  obtain ⟨hr₁,hr₂⟩ := rows_CR σ p
  constructor
  · intro h
    obtain ⟨L, hL⟩ := CRCoordinates.factor_through_pair hp hr₁ hr₂ h hb
    change ∀ v, L (coframe σ p v) = D v at hL
    intro v
    rw [← hL, coframe_J σ hp, map_smul, hL, smul_eq_mul]
  · intro h
    let e := ContinuousLinearEquiv.ofBijective (coframe σ p)
      (LinearMap.ker_eq_bot.mpr hb.1) (LinearMap.range_eq_top.mpr hb.2)
    let D' := D.comp e.symm.toContinuousLinearMap
    have hd' (v : E) : D' (I • v) = I * D' v := by
      obtain ⟨w, rfl⟩ := e.surjective v
      have eq : I • e w = e (J σ p w) := (coframe_J σ hp w).symm
      simp [D', eq, h]
    let L := complexify D' hd'
    have eq : (L.restrictScalars ℝ).comp (coframe σ p) = D := by
      apply ContinuousLinearMap.ext
      intro w
      change D (e.symm (e w)) = D w
      rw [e.symm_apply_apply]
    rw [← eq]
    exact CRCoordinates.cr_of_complex_linear hr₁ hr₂ L

/-- On the punctured open disk this extension is the given log-polar moving frame. -/
theorem polar_intertwines (σ : ℂ → ℝ) (p : ConformalFrame.Chart) (hp : p.2.2 < 0)
    (v : ConformalFrame.Chart) :
    fderiv ℝ PolarCR.polar p (ConformalFrame.J σ p v) =
      J σ (PolarCR.polar p) (fderiv ℝ PolarCR.polar p v) := by
  have hu : ‖ConformalFrame.unit p.2.1‖ = 1 := by
    rw [← sq_eq_sq₀ (norm_nonneg _) zero_le_one, ← Complex.normSq_eq_norm_sq]
    simp [ConformalFrame.unit, Complex.normSq_apply, Complex.real_smul,
      -Complex.ofReal_cos, -Complex.ofReal_sin]
    nlinarith [Real.sin_sq_add_cos_sq p.2.1]
  have hw : ‖(PolarCR.polar p).2‖ < 1 := by
    simpa [PolarCR.polar, norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le, hu] using Real.exp_lt_one_iff.mpr hp
  apply (coframe_bijective σ hw).1
  rw [coframe_J σ hw]
  have rows := rows_CR σ (PolarCR.polar p)
  exact Prod.ext ((PolarCR.satisfiesCR_iff p hp _).mp rows.1 v)
    ((PolarCR.satisfiesCR_iff p hp _).mp rows.2 v)

end TransportOkaGrauert.PhysicalStein
