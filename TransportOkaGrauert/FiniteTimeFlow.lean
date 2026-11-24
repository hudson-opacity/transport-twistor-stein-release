import TransportOkaGrauert.VolterraInverse

/-! # Smooth dependence at arbitrary finite travel times
The derivative of the Picard equation in the path variable is an invertible
Volterra operator even on a long interval. -/
namespace TransportOkaGrauert.FiniteTimeFlow
noncomputable section
open SmoothLocalFlow Set Filter Metric MeasureTheory
open scoped ContDiff Topology unitInterval
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

private theorem implicitAt (X : E → E) (hX : ContDiff ℝ ∞ X) (p : (E × ℝ) × Path E) :
    IsContDiffImplicitAt ∞ (residual X hX) (fderiv ℝ (residual X hX) p) p := by
  let D : Path (E →L[ℝ] E) :=
    ((⟨fderiv ℝ X,hX.continuous_fderiv (by simp)⟩ : C(E,E →L[ℝ] E))).comp p.2
  let R := residual X hX
  have smoothR := smooth_residual X hX
  have dR := (smoothR.differentiable (by simp) p).hasFDerivAt
  have dX := SmoothPathComposition.derivative X hX p.2
  have dV := (integration (E := E)).hasFDerivAt.comp p.2 dX
  have sliced := ((hasFDerivAt_id (𝕜 := ℝ) p.2).sub_const (ContinuousMap.const unitInterval p.1.1)).sub
    (dV.const_smul p.1.2)
  have emb := (hasFDerivAt_const (𝕜 := ℝ) p.1 p.2).prodMk (hasFDerivAt_id (𝕜 := ℝ) p.2)
  have along := dR.comp p.2 emb
  have eq : (fderiv ℝ R p).comp (ContinuousLinearMap.inr ℝ (E × ℝ) (Path E)) =
      1 - VolterraInverse.operator (p.1.2 • D) := by
    have h := along.unique sliced
    ext v s
    have h' := congrArg (fun L : Path E →L[ℝ] Path E => L v s) h
    change ((fderiv ℝ R p) (0,v)) s =
      (v - p.1.2 • integration ((SmoothPathComposition.evaluation
      (K := unitInterval) (E := E) (F := E) D) v)) s at h'
    rw [show VolterraInverse.operator (p.1.2 • D) = p.1.2 • VolterraInverse.operator D by
      unfold VolterraInverse.operator
      rw [map_smul,ContinuousLinearMap.comp_smul]]
    exact h'
  exact ⟨dR,smoothR.contDiffAt,by rw [eq]; exact VolterraInverse.bijective _,by simp⟩

/-- A unique solution for each normalized path automatically depends smoothly
on both initial state and time, without a travel-time bound. -/
theorem smooth_family (X : E → E) (hX : ContDiff ℝ ∞ X)
    (existsUniquePath : ∀ yt : E × ℝ, ∃! v : Path E, residual X hX (yt,v) = 0) :
    ∃ P : E × ℝ → Path E, ContDiff ℝ ∞ P ∧ ∀ yt, residual X hX (yt,P yt) = 0 := by
  choose P hP using fun yt => (existsUniquePath yt).exists
  refine ⟨P,contDiff_iff_contDiffAt.mpr (fun yt => ?_),hP⟩
  let H := implicitAt X hX (yt,P yt)
  have hz := hP yt
  apply H.contDiffAt_implicitFunction.congr_of_eventuallyEq
  filter_upwards [H.apply_implicitFunction] with y hy
  exact (existsUniquePath y).unique (hP y) (hy.trans hz)

/-- The rescaled equation along an ordinary velocity trajectory. -/
theorem curve_solves {X : E → E} (hX : ContDiff ℝ ∞ X) (γ : ℝ → E) (t : ℝ)
    (der : ∀ s ∈ Icc (0:ℝ) 1, HasDerivAt γ (X (γ (t*s))) (t*s)) :
    ∃ v : Path E, (∀ s, v s = γ (t*s.val)) ∧ residual X hX ((γ 0,t),v) = 0 := by
  let g (s : ℝ) := γ (t*s)
  have dg (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) : HasDerivAt g (t • X (g s)) s := by
    simpa only [mul_one] using (der s hs).scomp s ((hasDerivAt_id s).const_mul t)
  have cg : ContinuousOn g (Icc 0 1) := fun s hs => (dg s hs).continuousAt.continuousWithinAt
  let v : Path E := ⟨fun s => g s.val,cg.restrict⟩
  refine ⟨v,fun s => rfl,ContinuousMap.ext (fun s => ?_)⟩
  let Y (r : ℝ) := X (v (projIcc 0 1 zero_le_one r))
  have cyc : Continuous Y := hX.continuous.comp (continuous_clamped v)
  have deriv (r : ℝ) (hr : r ∈ uIcc 0 s.val) : HasDerivAt g (t • Y r) r := by
    rw [uIcc_of_le s.property.1] at hr
    have h1 : r ∈ Icc (0:ℝ) 1 := ⟨hr.1,hr.2.trans s.property.2⟩
    simpa only [Y,projIcc_of_mem _ h1,v,ContinuousMap.coe_mk] using dg r h1
  have integ := intervalIntegral.integral_eq_sub_of_hasDerivAt deriv
    ((continuous_const.smul cyc).intervalIntegrable _ _)
  rw [intervalIntegral.integral_smul] at integ
  change g s.val - γ 0 - t • (∫ r : ℝ in 0..s.val, Y r) = 0
  rw [integ,show g 0 = γ 0 by simp [g],sub_self]

end
end TransportOkaGrauert.FiniteTimeFlow
