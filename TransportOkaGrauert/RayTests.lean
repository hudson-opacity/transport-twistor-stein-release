import TransportOkaGrauert.WeightContinuity
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Tactic

/-!
# Scalar test pairings of weighted ray integrals

A compact phase space carries the weight and the test section. A point of
the ray-label space selects a curve on the unit interval and its length.
The outer Bochner integral is taken against an arbitrary finite measure.
Clamping the real integration variable extends each path constantly past
its endpoints and does not change the integral on the unit interval.
-/
namespace TransportOkaGrauert.RayTests
noncomputable section

open MeasureTheory Set
open scoped InnerProductSpace

abbrev UnitSegment := Icc (0 : ℝ) 1

variable {P B E : Type*} [TopologicalSpace P] [CompactSpace P]
    [TopologicalSpace B] [NormedAddCommGroup E] [InnerProductSpace ℂ E]

abbrev Weight (P E : Type*) [TopologicalSpace P] [NormedAddCommGroup E] [InnerProductSpace ℂ E] :=
  C(P, E →L[ℂ] E)

structure Geometry (B P : Type*) [TopologicalSpace B] [TopologicalSpace P] where
  path : C(B × UnitSegment, P)
  length : C(B, ℝ)
  nonnegative : ∀ b, 0 ≤ length b

namespace Geometry
variable (g : Geometry B P)

def point (b : B) (t : ℝ) : P := g.path (b, projIcc 0 1 zero_le_one t)

omit [CompactSpace P] in
private theorem point_continuous : Continuous (fun p : B × ℝ => g.point p.1 p.2) :=
  g.path.continuous.comp (continuous_fst.prodMk (continuous_projIcc.comp continuous_snd))

/-- The weighted integral of the test section over a finite ray. -/
def ray (W : Weight P E) (f : C(P,E)) (b : B) : E :=
  g.length b • ∫ t in (0 : ℝ)..1, W (g.point b t) (f (g.point b t))

theorem ray_norm_le (W : Weight P E) (f : C(P,E)) (b : B) :
    ‖g.ray W f b‖ ≤ g.length b * (‖W‖ * ‖f‖) := by
  have h : ∀ t : ℝ, ‖W (g.point b t) (f (g.point b t))‖ ≤ ‖W‖ * ‖f‖ := fun t =>
    ((W _).le_opNorm _).trans (mul_le_mul (W.norm_coe_le_norm _) (f.norm_coe_le_norm _)
      (norm_nonneg _) (norm_nonneg W))
  rw [ray, norm_smul, Real.norm_eq_abs, abs_of_nonneg (g.nonnegative b)]
  apply mul_le_mul_of_nonneg_left _ (g.nonnegative b)
  simpa using intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (fun t _ => h t)

/-- Joint continuity in the entire sup-norm weight and the ray label. -/
theorem ray_continuous (f : C(P,E)) :
    Continuous (fun p : Weight P E × B => g.ray p.1 f p.2) := by
  apply (g.length.continuous.comp continuous_snd).smul
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  change Continuous (fun p : (Weight P E × B) × ℝ =>
    p.1.1 (g.point p.1.2 p.2) (f (g.point p.1.2 p.2)))
  have hp : Continuous (fun p : (Weight P E × B) × ℝ => g.point p.1.2 p.2) :=
    g.point_continuous.comp ((continuous_snd.comp continuous_fst).prodMk continuous_snd)
  exact (continuous_eval.comp ((continuous_fst.comp continuous_fst).prodMk hp)).clm_apply
    (f.continuous.comp hp)


omit [CompactSpace P] in
private theorem ray_integrable_time (W : Weight P E) (f : C(P,E)) (b : B) :
    IntervalIntegrable (fun t => W (g.point b t) (f (g.point b t))) volume 0 1 := by
  have hp : Continuous (g.point b) := g.point_continuous.comp (continuous_const.prodMk continuous_id)
  exact ((W.continuous.comp hp).clm_apply (f.continuous.comp hp)).intervalIntegrable _ _

omit [CompactSpace P] in
theorem ray_add (W V : Weight P E) (f : C(P,E)) (b : B) :
    g.ray (W + V) f b = g.ray W f b + g.ray V f b := by
  simp only [ray, ContinuousMap.add_apply, ContinuousLinearMap.add_apply,
    intervalIntegral.integral_add (g.ray_integrable_time W f b) (g.ray_integrable_time V f b), smul_add]

omit [CompactSpace P] in
theorem ray_smul (c : ℂ) (W : Weight P E) (f : C(P,E)) (b : B) :
    g.ray (c • W) f b = c • g.ray W f b := by
  simp only [ray, ContinuousMap.smul_apply, ContinuousLinearMap.smul_apply, intervalIntegral.integral_smul]
  exact smul_comm _ _ _

variable [MeasurableSpace B]

/-- The weak cross-normal test, with the complex conjugation in its first slot. -/
def pairing (μ : Measure B) (W V : Weight P E) (h f : C(P,E)) : ℂ :=
  ∫ b, ⟪g.ray W h b, g.ray V f b⟫_ℂ ∂μ

/-- Uniform sup-norm bound with the total ray measure and two length factors. -/
theorem pairing_norm_le (μ : Measure B) [IsFiniteMeasure μ] (W V : Weight P E)
    (h f : C(P,E)) {L : ℝ} (lengthBound : ∀ b, g.length b ≤ L) :
    ‖g.pairing μ W V h f‖ ≤ μ.real univ * L^2 * ‖W‖ * ‖V‖ * ‖h‖ * ‖f‖ := by
  have hbound (b : B) :
      ‖⟪g.ray W h b, g.ray V f b⟫_ℂ‖ ≤ L^2 * ‖W‖ * ‖V‖ * ‖h‖ * ‖f‖ := by
    have hL : 0 ≤ L := (g.nonnegative b).trans (lengthBound b)
    calc
      _ ≤ ‖g.ray W h b‖ * ‖g.ray V f b‖ := norm_inner_le_norm _ _
      _ ≤ (L * (‖W‖ * ‖h‖)) * (L * (‖V‖ * ‖f‖)) := by
        apply mul_le_mul _ _ (norm_nonneg _) (by positivity)
        · exact (g.ray_norm_le W h b).trans (by gcongr; apply lengthBound)
        · exact (g.ray_norm_le V f b).trans (by gcongr; apply lengthBound)
      _ = _ := by ring
  have hb := norm_integral_le_of_norm_le_const (μ := μ) (Filter.Eventually.of_forall hbound)
  exact hb.trans_eq (by ring)

section Continuity
variable [T2Space B] [CompactSpace B] [OpensMeasurableSpace B]

/-- Integration against a finite measure is continuous on continuous test
functions in the uniform norm. -/
private def scalarIntegral (μ : Measure B) [IsFiniteMeasure μ] : C(B,ℂ) →L[ℝ] ℂ := by
  have hInt (f : C(B,ℂ)) : Integrable f μ := by
    simpa only [integrableOn_univ] using f.continuous.continuousOn.integrableOn_compact
      (μ := μ) isCompact_univ
  let ℓ : C(B,ℂ) →ₗ[ℝ] ℂ := {
    toFun := fun f => ∫ b, f b ∂μ
    map_add' := fun f h => integral_add (hInt f) (hInt h)
    map_smul' := fun c f => integral_smul c f }
  exact ℓ.mkContinuous (μ.real univ) (fun f => by
    simpa only [mul_comm] using norm_integral_le_of_norm_le_const (μ := μ)
      (Filter.Eventually.of_forall f.norm_coe_le_norm))

/-- Both weights may vary jointly. The Bochner integral construction and
joint continuity of the rays imply continuity of the scalar test pairing. -/
theorem pairing_continuous (μ : Measure B) [IsFiniteMeasure μ] (h f : C(P,E)) :
    Continuous (fun p : Weight P E × Weight P E => g.pairing μ p.1 p.2 h f) := by
  let integrand (p : Weight P E × Weight P E) : C(B,ℂ) :=
    ⟨fun b => ⟪g.ray p.1 h b, g.ray p.2 f b⟫_ℂ,
      ((g.ray_continuous h).comp (continuous_const.prodMk continuous_id)).inner
        ((g.ray_continuous f).comp (continuous_const.prodMk continuous_id))⟩
  change Continuous ((scalarIntegral μ) ∘ integrand)
  apply (scalarIntegral μ).continuous.comp
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact ((g.ray_continuous h).comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd)).inner
    ((g.ray_continuous f).comp ((continuous_snd.comp continuous_fst).prodMk continuous_snd))

private theorem test_integrable (μ : Measure B) [IsFiniteMeasure μ] (W V : Weight P E)
    (h f : C(P,E)) : Integrable (fun b => ⟪g.ray W h b, g.ray V f b⟫_ℂ) μ := by
  have hc : Continuous (fun b => ⟪g.ray W h b, g.ray V f b⟫_ℂ) :=
    ((g.ray_continuous h).comp (continuous_const.prodMk continuous_id)).inner
      ((g.ray_continuous f).comp (continuous_const.prodMk continuous_id))
  simpa only [integrableOn_univ] using hc.continuousOn.integrableOn_compact (μ := μ) isCompact_univ

/-- This test is conjugate-linear in its first weight and linear in its
second, independently of whether any Sobolev realization has been built. -/
def sesquilinearPairing (μ : Measure B) [IsFiniteMeasure μ] (h f : C(P,E)) :
    Weight P E →ₗ⋆[ℂ] Weight P E →ₗ[ℂ] ℂ where
  toFun W := {
    toFun := fun V => g.pairing μ W V h f
    map_add' := fun U V => by
      simp only [pairing, ray_add, inner_add_right]
      exact integral_add (g.test_integrable μ W U h f) (g.test_integrable μ W V h f)
    map_smul' := fun c V => by
      simp [pairing, ray_smul, inner_smul_right, integral_const_mul] }
  map_add' U V := by
    ext W
    change g.pairing μ (U+V) W h f = g.pairing μ U W h f + g.pairing μ V W h f
    simp only [pairing, ray_add, inner_add_left]
    exact integral_add (g.test_integrable μ U W h f) (g.test_integrable μ V W h f)
  map_smul' c U := by
    ext W
    change g.pairing μ (c • U) W h f = (starRingEnd ℂ c) * g.pairing μ U W h f
    simp [pairing, ray_smul, inner_smul_left, integral_const_mul]

/-- A fixed-weight bounded Sobolev realization that agrees with the ray
pairing on norm-dense source and dual tests depends jointly continuously
on both weights in operator norm. The smooth weight topology only needs to
control the uniform topology on its continuous representatives. -/
theorem operatorNorm_of_test_realization (μ : Measure B) [IsFiniteMeasure μ]
    {W S Z : Type*} [AddCommGroup W] [Module ℝ W] [UniformSpace W] [IsUniformAddGroup W]
    [ContinuousSMul ℝ W] [BaireSpace W] [FirstCountableTopology W]
    [NormedAddCommGroup S] [NormedSpace ℝ S] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (N : W →ₗ[ℝ] W →ₗ[ℝ] (S →L[ℝ] Z)) (weight : W → Weight P E) (hw : Continuous weight)
    {s : Set S} {d : Set (Z →L[ℝ] ℝ)} (hs : Dense s) (hd : Dense d)
    (test : ∀ x ∈ s, ∀ l ∈ d, ∃ h f : C(P,E), ∀ u v,
      l (N u v x) = (g.pairing μ (weight u) (weight v) h f).re) :
    Continuous (fun p : W × W => N p.1 p.2) ∧ Continuous (fun w => N w w) := by
  apply WeightContinuity.polarized_operatorNorm_continuous N hs hd
  · intro v x hx l hl
    obtain ⟨h, f, he⟩ := test x hx l hl
    simp only [he]
    exact Complex.continuous_re.comp ((g.pairing_continuous μ h f).comp (hw.prodMk continuous_const))
  · intro u x hx l hl
    obtain ⟨h, f, he⟩ := test x hx l hl
    simp only [he]
    exact Complex.continuous_re.comp ((g.pairing_continuous μ h f).comp (continuous_const.prodMk hw))

end Continuity
end Geometry
end
end TransportOkaGrauert.RayTests
