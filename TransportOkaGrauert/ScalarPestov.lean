import TransportOkaGrauert.ConformalFrame
import TransportOkaGrauert.ScalarIndexForm

/-! # The local Pestov energy identity

All derivatives in the three flux terms use the geodesic, horizontal and
vertical fields of the conformal metric.
-/
noncomputable section
namespace TransportOkaGrauert.ScalarPestov
open ConformalFrame FrameLevi VectorField SimpleDiskTarget
open scoped ContDiff

abbrev speed (σ : ℂ → ℝ) := along (X σ)
abbrev horizontal (σ : ℂ → ℝ) := along (H σ)
abbrev vertical := along V

theorem smooth_along {P : Chart → Chart} {f : Chart → ℝ} (hP : ContDiff ℝ ∞ P)
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (along P f) :=
  (hf.fderiv_right (m := ∞) (by simp)).clm_apply hP

theorem product_rule (P : Chart → Chart) {f g : Chart → ℝ} {p : Chart}
    (df : DifferentiableAt ℝ f p) (dg : DifferentiableAt ℝ g p) :
    along P (fun q => f q * g q) p = along P f p * g p + f p * along P g p := by
  simp only [along,fderiv_fun_mul df dg,ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
  ring

/-- Pointwise Pestov identity including the three explicit divergence terms. -/
theorem flux_identity {σ : ℂ → ℝ} (hs : ContDiff ℝ ∞ σ) {u : Chart → ℝ}
    (hu : ContDiff ℝ ∞ u) (p : Chart) :
    vertical (speed σ u) p ^ 2 - speed σ (vertical u) p ^ 2 =
      speed σ u p ^ 2 - curvature σ p.1 * vertical u p ^ 2 +
      vertical (fun q => speed σ u q * horizontal σ u q) p +
      speed σ (fun q => vertical u q * horizontal σ u q) p -
      horizontal σ (fun q => speed σ u q * vertical u q) p := by
  have hX := (smooth_XH hs).1
  have hH := (smooth_XH hs).2
  have hV : ContDiff ℝ ∞ V := contDiff_const
  have b (P Q : Chart → Chart) (dP : ContDiff ℝ ∞ P) (dQ : ContDiff ℝ ∞ Q) :
      fderiv ℝ u p (lieBracket ℝ P Q p) = along P (along Q u) p - along Q (along P u) p :=
    fderiv_apply_lieBracket (hu.contDiffAt (x := p) |>.of_le (show (2:WithTop ℕ∞) ≤ ∞ by decide))
      (by norm_num) (dQ.differentiable (by simp) p) (dP.differentiable (by simp) p)
  obtain ⟨vx,hv,xh,_⟩ := brackets hs p
  have e₁ := b V (X σ) hV hX
  have e₂ := b (H σ) V hH hV
  have e₃ := b (X σ) (H σ) hX hH
  rw [vx] at e₁
  rw [hv] at e₂
  rw [xh,map_smul,smul_eq_mul] at e₃
  change horizontal σ u p = vertical (speed σ u) p - speed σ (vertical u) p at e₁
  change speed σ u p = horizontal σ (vertical u) p - vertical (horizontal σ u) p at e₂
  change curvature σ p.1 * vertical u p = speed σ (horizontal σ u) p - horizontal σ (speed σ u) p at e₃
  have dA := (smooth_along hX hu).differentiable (by simp) p
  have dB := (smooth_along hH hu).differentiable (by simp) p
  have dC := (smooth_along hV hu).differentiable (by simp) p
  simp only [vertical,speed,horizontal] at e₁ e₂ e₃ ⊢
  rw [product_rule V dA dB, product_rule (X σ) dC dB, product_rule (H σ) dA dC]
  linear_combination -(along V (along (X σ) u) p + along (X σ) (along V u) p) * e₁ -
    along (X σ) u p * e₂ + along V u p * e₃

end TransportOkaGrauert.ScalarPestov
