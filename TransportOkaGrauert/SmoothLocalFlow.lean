import TransportOkaGrauert.SmoothPathComposition
import TransportOkaGrauert.ChartRegularity
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.ODE.PicardLindelof

/-! # Smooth dependence of a finite-time geodesic on its initial data
Solve the rescaled Picard equation on the fixed unit interval. At time zero
its derivative in the path variable is the identity. -/
namespace TransportOkaGrauert.SmoothLocalFlow
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology unitInterval
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

abbrev Path (E : Type) [TopologicalSpace E] := C(unitInterval,E)

def clamped (v : Path E) (s : ℝ) := v (projIcc 0 1 zero_le_one s)

omit [NormedSpace ℝ E] [CompleteSpace E] in
theorem continuous_clamped (v : Path E) : Continuous (clamped v) :=
  v.continuous.comp continuous_projIcc

private def primitive (v : Path E) : Path E where
  toFun s := ∫ t : ℝ in 0..s.val, clamped v t
  continuous_toFun := (intervalIntegral.continuous_primitive
    (fun _ _ => (continuous_clamped v).intervalIntegrable _ _) 0).comp continuous_subtype_val

private def primitiveLinear : Path E →ₗ[ℝ] Path E where
  toFun := primitive
  map_add' f g := ContinuousMap.ext fun _ => intervalIntegral.integral_add
    ((continuous_clamped f).intervalIntegrable _ _) ((continuous_clamped g).intervalIntegrable _ _)
  map_smul' r _ := ContinuousMap.ext fun _ => intervalIntegral.integral_smul r _

def integration : Path E →L[ℝ] Path E := (primitiveLinear (E := E)).mkContinuous 1 (by
  intro v
  rw [one_mul]
  apply (ContinuousMap.norm_le (primitive v) (norm_nonneg v)).mpr
  intro s
  have b := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := s.val)
    (fun x _ => v.norm_coe_le_norm (projIcc 0 1 zero_le_one x))
  exact b.trans (by simpa only [sub_zero,abs_of_nonneg s.property.1] using
    (mul_le_mul_of_nonneg_left s.property.2 (norm_nonneg v)).trans (by simp)))

def residual (X : E → E) (hX : ContDiff ℝ ∞ X) (p : (E × ℝ) × Path E) : Path E :=
  p.2 - ContinuousMap.const unitInterval p.1.1 -
    p.1.2 • integration (ContinuousMap.comp (⟨X,hX.continuous⟩ : C(E,E)) p.2)

omit [CompleteSpace E] in
theorem smooth_residual (X : E → E) (hX : ContDiff ℝ ∞ X) :
    ContDiff ℝ ∞ (residual X hX) := by
  have h := (SmoothPathComposition.smooth (K := unitInterval) X hX).comp
    (contDiff_snd (E := E × ℝ))
  exact (contDiff_snd.sub ((ContinuousLinearMap.const ℝ unitInterval (M := E)).contDiff.comp
    (contDiff_fst.comp contDiff_fst))).sub ((contDiff_snd.comp contDiff_fst).smul
    ((integration (E := E)).contDiff.comp h))

/-- Solve the nonlinear integral equation with jointly smooth dependence of
the entire normalized path on the initial state and the time step. -/
theorem exists_smooth_paths (X : E → E) (hX : ContDiff ℝ ∞ X) (a : E) :
    ∃ P : E × ℝ → Path E, ContDiffAt ℝ ∞ P (a,0) ∧
      (∀ᶠ yt in 𝓝 (a,(0:ℝ)), residual X hX (yt,P yt) = 0) ∧
      ∀ᶠ pair in 𝓝 ((a,(0:ℝ)), ContinuousMap.const unitInterval a),
        residual X hX pair = 0 → P pair.1 = pair.2 := by
  let v := ContinuousMap.const unitInterval a
  let p := ((a,(0:ℝ)),v)
  let R := residual X hX
  have smoothR := smooth_residual X hX
  have derivR := (smoothR.differentiable (by simp) p).hasFDerivAt
  let inr := ContinuousLinearMap.inr ℝ (E × ℝ) (Path E)
  have D : (fderiv ℝ R p).comp inr = ContinuousLinearMap.id ℝ (Path E) := by
    have slice : HasFDerivAt (fun b : Path E => ((a,(0:ℝ)),b)) inr v :=
      by
        convert (hasFDerivAt_const (𝕜 := ℝ) (a,(0:ℝ)) v).prodMk (hasFDerivAt_id (𝕜 := ℝ) v) using 1
    have chain := derivR.comp v slice
    have simpR : (residual X hX ∘ (fun b : Path E => ((a,(0:ℝ)),b))) =
        (fun b : Path E => b-v) := by funext b; simp [residual,v]
    rw [simpR] at chain
    exact chain.unique ((hasFDerivAt_id v).sub_const v)
  have imp : IsContDiffImplicitAt ∞ R (fderiv ℝ R p) p :=
    ⟨derivR,smoothR.contDiffAt,by change Function.Bijective ((fderiv ℝ R p).comp inr); rw [D]; exact Function.bijective_id,by simp⟩
  have zero : R p = 0 := by simp [R,p,v,residual]
  exact ⟨imp.implicitFunction, imp.contDiffAt_implicitFunction,
    zero ▸ imp.apply_implicitFunction,zero ▸ imp.eventually_implicitFunction_apply_eq⟩

end
end TransportOkaGrauert.SmoothLocalFlow
