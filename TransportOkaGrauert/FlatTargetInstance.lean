import TransportOkaGrauert.SimpleDiskTarget
import TransportOkaGrauert.TwistorDisk
import TransportOkaGrauert.UpperDisk
import TransportOkaGrauert.DiskSeries

/-! The explicit Euclidean constructions satisfy the chart-level smoothness,
Fourier support, and geodesic transport conditions. -/
namespace TransportOkaGrauert.FlatTargetInstance

noncomputable section
open scoped ComplexConjugate ContDiff

private theorem unit_norm_identity (v : Circle) : (v : ℂ) * conj (v : ℂ) = 1 := by
  rw [← Circle.coe_inv_eq_conj, Circle.coe_inv, mul_inv_cancel₀ v.coe_ne_zero]

/-- For the Euclidean metric the angular drift vanishes identically. -/
theorem geodesicX_euclidean (f : ℂ → Circle → ℂ) (z : ℂ) (v : Circle) :
    Isothermal.geodesicX (fun _ => 0) f z v = Fourier.flatX f z v := by
  simp [Isothermal.geodesicX, Isothermal.angularDrift]

/-- The transport equation in the flat isothermal chart, in each matrix entry. -/
theorem polynomial_chart_transport {n : ℕ} (a : UpperDisk.Coefficients n) (z : ℂ)
    (v : Circle) (i j : Fin n) :
    Isothermal.geodesicX (fun _ => 0) (fun x w => UpperDisk.frame a x w i j) z v +
      (UpperDisk.field a z v * UpperDisk.frame a z v) i j = 0 := by
  rw [geodesicX_euclidean]
  have h := (UpperDisk.regularity a i j).1.comp
    (contDiff_id.prodMk (contDiff_const (c := (v : ℂ))))
  have hbase : DifferentiableAt ℝ (fun x => UpperDisk.frame a x v i j) z :=
    (h.differentiable (by decide)).differentiableAt
  have he := (TwistorDisk.line_derivative (fun x w => UpperDisk.frame a x w i j) z v hbase).unique
    (UpperDisk.geodesic_transport a z v (unit_norm_identity v) i j)
  exact eq_neg_iff_add_eq_zero.mp he

private theorem circleAngle_smooth : ContDiff ℝ ∞ (fun t : ℝ => (Circle.exp t : ℂ)) := by
  convert contDiff_circleMap 0 1 using 1
  funext t
  simp [circleMap, Circle.coe_exp]

private theorem angular_restriction {f : ℂ → ℂ → ℂ}
    (hf : ContDiff ℝ ∞ (fun p : ℂ × ℂ => f p.1 p.2)) :
    ContDiff ℝ ∞ (fun p : ℂ × ℝ => f p.1 (Circle.exp p.2)) :=
  hf.comp (contDiff_fst.prodMk (circleAngle_smooth.comp contDiff_snd))

private theorem eval_smooth (P : List PolynomialDisk.Monomial) :
    ContDiff ℝ ∞ (fun p : ℂ × ℂ => PolynomialDisk.eval P p.1 p.2) := by
  have hs : ContDiff ℝ ∞ (fun p : ℂ × ℂ => conj p.1) :=
    Complex.conjCLE.contDiff.comp contDiff_fst
  have ht : ContDiff ℝ ∞ (fun p : ℂ × ℂ => conj p.2) :=
    Complex.conjCLE.contDiff.comp contDiff_snd
  induction P with
  | nil => exact contDiff_const
  | cons m ms ih =>
    change ContDiff ℝ ∞ (fun p : ℂ × ℂ => m.eval p.1 p.2 + PolynomialDisk.eval ms p.1 p.2)
    apply ContDiff.add _ ih
    unfold PolynomialDisk.Monomial.eval
    fun_prop

private theorem periodic_velocity (t : ℝ) :
    AddCircle.toCircle (t : DiskSeries.Angle) = Circle.exp t := by
  rw [AddCircle.toCircle_apply_mk]
  simp [Real.pi_ne_zero]

open scoped Matrix.Norms.Operator
open FlatMatrix

private def entryAt {n : ℕ} (i j : Fin n) : Mat n →L[ℝ] ℂ :=
  ⟨Matrix.entryLinearMap ℝ ℂ i j, (continuous_apply j).comp (continuous_apply i)⟩

private theorem regular_entry {n : ℕ} {f : ℂ → Mat n}
    (h : DiffContOnCl ℂ f (Metric.ball 0 1)) (i j : Fin n) :
    DiffContOnCl ℂ (fun w => f w i j) (Metric.ball 0 1) := by
  let ev : Mat n →L[ℂ] ℂ := ⟨Matrix.entryLinearMap ℂ ℂ i j, (continuous_apply j).comp (continuous_apply i)⟩
  exact ⟨ev.differentiable.comp_differentiableOn h.differentiableOn,
    ev.continuous.comp_continuousOn h.continuousOn⟩

open SimpleDiskTarget

/-- The Euclidean chart target, including both admissibility hypotheses, for
every strictly upper triangular polynomial attenuation in every finite rank. -/
theorem polynomial {n : ℕ} (a : UpperDisk.Coefficients n) :
    let A : Field n := fun z v => UpperDisk.field a z v
    SmoothToBoundary A ∧ ModesFrom (-1) A ∧ ∃ F G : Field n, IsFrame (fun _ => 0) A F G := by
  dsimp only
  refine ⟨?_, fun z _ i j k hk => UpperDisk.field_modes a z i j k hk, ?_⟩
  · intro z _ θ i j
    by_cases h : i < j
    · simpa [UpperDisk.field, h] using (angular_restriction (eval_smooth (a i j))).contDiffAt
        (x := (z, θ))
    · simp [UpperDisk.field, h, contDiffAt_const]
  · refine ⟨fun z v => UpperDisk.frame a z v, fun z v => UpperDisk.inverseFrame a z v, ?_⟩
    exact {
      smoothF := fun _ _ _ i j => (angular_restriction (f := fun z w => UpperDisk.frame a z w i j) (UpperDisk.regularity a i j).1).contDiffAt
      smoothG := fun _ _ _ i j => (angular_restriction (f := fun z w => UpperDisk.inverseFrame a z w i j) (UpperDisk.regularity a i j).2.1).contDiffAt
      modesF := fun z _ i j k hk => (UpperDisk.frame_modes a z i j k hk).1
      modesG := fun z _ i j k hk => (UpperDisk.frame_modes a z i j k hk).2
      inverses := fun z _ w => UpperDisk.inverse_identities a z w
      transport := fun z _ w i j => polynomial_chart_transport a z w i j }

local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

/-- The same chart conclusion for all smooth direction-only matrix profiles of
arbitrary rank and unrestricted upper Fourier frequency. -/
theorem directionOnly {n : ℕ} (a : C(Circle, FlatMatrix.Mat n))
    (smooth : ContDiff ℝ ∞ (fun t : ℝ => a (Circle.exp t)))
    (modes : ModesFrom (-1) (fun _ v => a v)) :
    ∃ F G : Field n, IsFrame (fun _ => 0) (fun _ v => a v) F G := by
  let b : C(DiskSeries.Angle, FlatMatrix.Mat n) := a.comp ⟨_, AddCircle.continuous_toCircle⟩
  have hs : ContDiff ℝ ∞ (fun t : ℝ => b (t : DiskSeries.Angle)) := by
    simpa only [b, ContinuousMap.comp_apply, ContinuousMap.coe_mk, periodic_velocity] using smooth
  have hm (i j : Fin n) (k : ℤ) (hk : k < -1) : fourierCoeff (DiskSeries.entry b i j) k = 0 :=
    modes 0 (by simp) i j k hk
  obtain ⟨F, G, ⟨hF, hG⟩, hregular, _, hInv, htransport⟩ :=
    DiskSeries.smooth_directionOnlyIntegratingFactor b hs hm
  simp only [periodic_velocity] at hF hG
  have hfs (i j : Fin n) :
      ContDiff ℝ ∞ (fun p : ℂ × ℝ => F p.1 (Circle.exp p.2) i j) := (entryAt i j).contDiff.comp hF
  have hgs (i j : Fin n) :
      ContDiff ℝ ∞ (fun p : ℂ × ℝ => G p.1 (Circle.exp p.2) i j) := (entryAt i j).contDiff.comp hG
  refine ⟨fun z w => F z w, fun z w => G z w, ?_⟩
  refine {
    smoothF := fun _ _ _ i j => (hfs i j).contDiffAt
    smoothG := fun _ _ _ i j => (hgs i j).contDiffAt
    modesF := fun z _ i j k hk => BoundaryModes.negativeMode_eq_zero (regular_entry (hregular z).1 i j) k hk
    modesG := fun z _ i j k hk => BoundaryModes.negativeMode_eq_zero (regular_entry (hregular z).2 i j) k hk
    inverses := fun z _ w => hInv z w
    transport := ?_ }
  intro z _ w i j
  rw [geodesicX_euclidean]
  let θ := Complex.arg (w : ℂ)
  have hw : Circle.exp θ = w := Circle.exp_arg w
  have hbase : DifferentiableAt ℝ (fun x => F x w i j) z := by
    have h := (hfs i j).comp (contDiff_id.prodMk (contDiff_const (c := θ)))
    simpa only [Function.comp_def, id_eq, hw] using (h.differentiable (by decide)).differentiableAt (x := z)
  have hl := (entryAt i j).hasFDerivAt.comp_hasDerivAt 0 (htransport z (θ : DiskSeries.Angle))
  have he : HasDerivAt (fun t : ℝ => F (z + t * w) w i j) (-(a w * F z w) i j) 0 := by
    simpa only [Function.comp_def, entryAt, ContinuousLinearMap.coe_mk', Matrix.entryLinearMap_apply,
      b, ContinuousMap.comp_apply, ContinuousMap.coe_mk, periodic_velocity, hw, Matrix.neg_apply] using hl
  exact eq_neg_iff_add_eq_zero.mp ((TwistorDisk.line_derivative (fun x v => F x v i j) z w hbase).unique he)

/-- For position-independent inputs the assumptions are exactly the two
analytic hypotheses in the general chart target. Boundary smoothness supplies
continuity on the circle and differentiability of the periodic angular lift. -/
theorem directionOnly_of_chart_data {n : ℕ} (a : Circle → FlatMatrix.Mat n)
    (smooth : SmoothToBoundary (fun _ v => a v)) (modes : ModesFrom (-1) (fun _ v => a v)) :
    ∃ F G : Field n, IsFrame (fun _ => 0) (fun _ v => a v) F G := by
  have he (i j : Fin n) : ContDiff ℝ ∞ (fun t : ℝ => a (Circle.exp t) i j) := by
    apply contDiff_iff_contDiffAt.mpr
    intro t
    exact (smooth 0 (by simp) t i j).comp t
      (contDiffAt_const (c := (0 : ℂ)) |>.prodMk contDiffAt_id)
  have hM : ContDiff ℝ ∞ (fun t : ℝ => a (Circle.exp t)) := by
    have h : ContDiff ℝ ∞ (fun t : ℝ =>
        ∑ i, ∑ j, a (Circle.exp t) i j • Matrix.single i j (1 : ℂ)) :=
      ContDiff.sum (fun i _ => ContDiff.sum (fun j _ => (he i j).smul contDiff_const))
    convert h using 1
    funext t
    simp only [Matrix.smul_single, smul_eq_mul, mul_one, Matrix.sum_sum_single]
    rfl
  have ha : Continuous a := Circle.isAddQuotientCoveringMap_exp.isOpenQuotientMap.isQuotientMap.continuous_iff.mpr
    hM.continuous
  exact directionOnly ⟨a, ha⟩ hM modes

end
end TransportOkaGrauert.FlatTargetInstance
