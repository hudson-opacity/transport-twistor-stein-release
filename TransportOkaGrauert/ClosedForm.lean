import TransportOkaGrauert.Isothermal
import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare

/-! Closed scalar one-forms in a conformal chart. The base potential is
constructed by the Poincaré lemma on an open convex neighborhood of the disk. -/
noncomputable section

namespace TransportOkaGrauert.ClosedForm

open scoped ContDiff
open Isothermal

/-- Restrict a complex-valued one-form to unit vectors of exp(2λ)|dz|². -/
def attenuation (lam : ℂ → ℝ) (form : ℂ → ℂ →L[ℝ] ℂ) (z : ℂ) (w : Circle) : ℂ :=
  (Real.exp (-lam z) : ℂ) * form z (w : ℂ)

/-- On any open convex chart, a smooth closed complex-valued one-form admits
a scalar frame, even for a spatially varying metric. Both frames are constant
on each velocity disk, hence holomorphic there. -/
theorem integrating_factor (lam : ℂ → ℝ) (s : Set ℂ) (hs : Convex ℝ s) (ho : IsOpen s)
    (form : ℂ → ℂ →L[ℝ] ℂ) (hform : ContDiffOn ℝ ∞ form s)
    (closed : ∀ z ∈ s, ∀ v w, fderiv ℝ form z v w = fderiv ℝ form z w v) :
    ∃ F G : ℂ → ℂ, ContDiffOn ℝ ∞ F s ∧ ContDiffOn ℝ ∞ G s ∧
      (∀ z, F z * G z = 1) ∧ ∀ z ∈ s, ∀ w : Circle,
        geodesicX lam (fun p _ => F p) z w + attenuation lam form z w * F z = 0 := by
  obtain ⟨u, hu⟩ := hs.exists_forall_hasFDerivAt_of_fderiv_symmetric ho
    (hform.differentiableOn (by simp)) closed
  have smooth : ContDiffOn ℝ ∞ u s :=
    (contDiffOn_infty_iff_fderiv_of_isOpen ho).mpr
      ⟨fun z hz => (hu z hz).differentiableAt.differentiableWithinAt,
        hform.congr (fun z hz => (hu z hz).fderiv)⟩
  refine ⟨fun z => Complex.exp (-u z), fun z => Complex.exp (u z), smooth.neg.cexp,
    smooth.cexp, fun z => by rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero], ?_⟩
  intro z hz w
  have hd := (hu z hz).neg.cexp.fderiv
  change fderiv ℝ (fun p => Complex.exp (-u p)) z = _ at hd
  simp only [geodesicX, Fourier.flatX, vertical, deriv_const, mul_zero, add_zero, hd,
    Pi.neg_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.neg_apply, smul_eq_mul, attenuation]
  ring

end TransportOkaGrauert.ClosedForm
