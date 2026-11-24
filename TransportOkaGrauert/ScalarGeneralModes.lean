import TransportOkaGrauert.ScalarGeneralCauchy
import TransportOkaGrauert.Isothermal

/-! Surjectivity of the two scalar one-mode operators in isothermal coordinates,
for every integer mode and every smooth conformal factor. -/
noncomputable section
namespace TransportOkaGrauert.ScalarGeneralModes
open Complex Metric Isothermal ScalarGeneralCauchy
open scoped ContDiff ComplexConjugate

private def weight (σ : ℂ → ℝ) (c : ℝ) (z : ℂ) : ℂ := (Real.exp (c * σ z) : ℂ)
private theorem smooth_weight {σ : ℂ → ℝ} (hs : ContDiff ℝ ∞ σ) (c : ℝ) : ContDiff ℝ ∞ (weight σ c) :=
  Complex.ofRealCLM.contDiff.comp ((contDiff_const.mul hs).exp)

private theorem weight_direction {σ : ℂ → ℝ} (hs : ContDiff ℝ ∞ σ) (z d : ℂ) (c : ℝ) :
    fderiv ℝ (weight σ c) z d = weight σ c z * (c : ℂ) * (fderiv ℝ σ z d : ℂ) := by
  have H := Complex.ofRealCLM.hasFDerivAt.comp z (((hs.differentiable (by simp) z).hasFDerivAt.const_mul c).exp)
  rw [show fderiv ℝ (weight σ c) z = _ from H.fderiv]
  change ((Real.exp (c * σ z) * (c * fderiv ℝ σ z d) : ℝ) : ℂ) = _
  simp [weight, mul_assoc]

private theorem weight_opposite (σ : ℂ → ℝ) (z : ℂ) (c : ℝ) :
    weight σ (-c) z * weight σ c z = 1 := by
  unfold weight
  rw [← Complex.ofReal_mul, ← Real.exp_add, neg_mul, neg_add_cancel, Real.exp_zero, Complex.ofReal_one]

private theorem lower_weight {σ : ℂ → ℝ} (hs : ContDiff ℝ ∞ σ) {u : ℂ → ℂ} (hu : ContDiff ℝ ∞ u)
    (z : ℂ) (k : ℤ) : lowering σ (fun p => weight σ (-(k:ℝ)) p * u p) z k =
      weight σ (-1) z * weight σ (-(k:ℝ)) z * twiceBar (fderiv ℝ u z) / 2 := by
  let c := -(k:ℝ)
  have hp := (((smooth_weight hs c).differentiable (by simp) z).hasFDerivAt.mul
    (hu.differentiable (by simp) z).hasFDerivAt).fderiv
  have hd (d : ℂ) : fderiv ℝ (fun p => weight σ c p * u p) z d =
      weight σ c z * fderiv ℝ u z d + u z * (weight σ c z * (c:ℂ) * (fderiv ℝ σ z d : ℂ)) := by
    change fderiv ℝ (weight σ c * u) z d = _
    rw [hp]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, weight_direction hs]
  change (Real.exp (-σ z) : ℂ) * (fderiv ℝ (fun p => weight σ c p * u p) z 1 / 2 -
    fderiv ℝ (fun p => weight σ c p * u p) z I / (2*I) +
    ((fderiv ℝ σ z I : ℂ)/2 + (fderiv ℝ σ z 1 : ℂ)/(2*I)) * (weight σ c z * u z) * ((k:ℂ)*I)) =
      weight σ (-1) z * weight σ c z * (fderiv ℝ u z 1 + I * fderiv ℝ u z I) / 2
  rw [hd, hd, show weight σ (-1) z = (Real.exp (-σ z) : ℂ) by simp [weight]]
  simp only [c, Complex.ofReal_neg, Complex.ofReal_intCast]
  field_simp [Complex.I_ne_zero]
  ring_nf
  simp [Complex.I_sq]
  ring

/-- The conformally rescaled velocity has no lowering component. -/
theorem lowering_metric_weight {σ : ℂ → ℝ} (hs : ContDiff ℝ ∞ σ) (z : ℂ) :
    lowering σ (fun y => (Real.exp (-σ y) : ℂ)) z 1 = 0 := by
  have h := lower_weight hs (u := fun _ => 1) contDiff_const z 1
  simpa [weight,twiceBar] using h

/-- Every smooth output coefficient in mode `k-1` is obtained by applying the
actual geodesic lowering operator to a globally smooth coefficient in mode `k`. -/
theorem lowering_surjective {σ : ℂ → ℝ} (hs : ContDiff ℝ ∞ σ) (k : ℤ) (q : ℂ → ℂ) (hq : ContDiff ℝ ∞ q) :
    ∃ a : ℂ → ℂ, ContDiff ℝ ∞ a ∧ ∀ z ∈ closedBall (0:ℂ) 1, lowering σ a z k = q z := by
  obtain ⟨u,hu,heq⟩ := exists_twiceBar_primitive (fun z => 2 * weight σ 1 z * weight σ (k:ℝ) z * q z)
    (((contDiff_const.mul (smooth_weight hs 1)).mul (smooth_weight hs (k:ℝ))).mul hq)
  refine ⟨fun z => weight σ (-(k:ℝ)) z * u z, (smooth_weight hs _).mul hu, ?_⟩
  intro z hz
  rw [lower_weight hs hu, heq z hz]
  have h₁ := weight_opposite σ z 1
  have hk := weight_opposite σ z (k:ℝ)
  linear_combination (norm := ring) (weight σ (-(k:ℝ)) z * weight σ (k:ℝ) z * q z) * h₁ + q z * hk

private theorem conjugate_operators {σ : ℂ → ℝ} {a : ℂ → ℂ} (ha : ContDiff ℝ ∞ a) (z : ℂ) (k : ℤ) :
    raising σ (fun p => conj (a p)) z k = conj (lowering σ a z (-k)) := by
  have hd := (Complex.conjCLE.hasFDerivAt.comp z (ha.differentiable (by simp) z).hasFDerivAt).fderiv
  have H (d : ℂ) : fderiv ℝ (fun p => conj (a p)) z d = conj (fderiv ℝ a z d) :=
    congrArg (fun L : ℂ →L[ℝ] ℂ => L d) hd
  change (Real.exp (-σ z) : ℂ) * (fderiv ℝ (fun p => conj (a p)) z 1 / 2 +
    fderiv ℝ (fun p => conj (a p)) z I / (2*I) +
    ((fderiv ℝ σ z I : ℂ)/2 - (fderiv ℝ σ z 1 : ℂ)/(2*I)) * conj (a z) * ((k:ℂ)*I)) =
    conj ((Real.exp (-σ z) : ℂ) * (fderiv ℝ a z 1 / 2 - fderiv ℝ a z I / (2*I) +
      ((fderiv ℝ σ z I : ℂ)/2 + (fderiv ℝ σ z 1 : ℂ)/(2*I)) * a z * (((-k:ℤ):ℂ)*I)))
  simp only [H, map_mul, map_add, map_sub, map_div₀, Complex.conj_I, Complex.conj_ofReal, map_ofNat,
    Int.cast_neg, map_neg, map_intCast]
  ring

/-- Every smooth output coefficient in mode `k+1` has a smooth input in mode `k`. -/
theorem raising_surjective {σ : ℂ → ℝ} (hs : ContDiff ℝ ∞ σ) (k : ℤ) (q : ℂ → ℂ) (hq : ContDiff ℝ ∞ q) :
    ∃ a : ℂ → ℂ, ContDiff ℝ ∞ a ∧ ∀ z ∈ closedBall (0:ℂ) 1, raising σ a z k = q z := by
  obtain ⟨a,ha,he⟩ := lowering_surjective hs (-k) (fun p => conj (q p)) (Complex.conjCLE.contDiff.comp hq)
  exact ⟨fun p => conj (a p), Complex.conjCLE.contDiff.comp ha, fun z hz => by rw [conjugate_operators ha, he z hz]; simp⟩

end TransportOkaGrauert.ScalarGeneralModes
