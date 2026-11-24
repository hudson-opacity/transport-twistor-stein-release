import TransportOkaGrauert.TwistorDisk
import TransportOkaGrauert.UpperDisk

/-!
# Holomorphic frames on the flat twistor disk for triangular polynomial fields

The polynomial numerator extends the boundary coefficient `w A` across
`w = 0`. We verify the horizontal equation on the closed disk for the
explicit frame in every rank. Its vertical equation is fiber holomorphicity.
-/

noncomputable section

namespace TransportOkaGrauert.UpperTwistor

open Complex Metric TwistorDisk FlatScalar
open scoped ComplexConjugate

/-- Fiber holomorphicity also holds for the real base derivative in each
fixed direction. This property is stable under the polynomial operations. -/
private structure RegularAt (z : ℂ) (f : ℂ → ℂ → ℂ) : Prop where
  base : ∀ w, DifferentiableAt ℝ (fun p => f p w) z
  fiber : Differentiable ℂ (f z)
  slope : ∀ d : ℂ, Differentiable ℂ (fun w => fderiv ℝ (fun p => f p w) z d)

private theorem baseOnly (z : ℂ) (g : ℂ → ℂ) (hg : DifferentiableAt ℝ g z) :
    RegularAt z (fun p _ => g p) :=
  ⟨fun _ => hg, differentiable_const _, fun _ => differentiable_const _⟩

private theorem velocityOnly (z : ℂ) (g : ℂ → ℂ) (hg : Differentiable ℂ g) :
    RegularAt z (fun _ w => g w) := by
  refine ⟨fun _ => differentiableAt_const _, hg, ?_⟩
  intro d
  simp

private theorem RegularAt.add {z : ℂ} {f g : ℂ → ℂ → ℂ} (hf : RegularAt z f) (hg : RegularAt z g) :
    RegularAt z (fun p w => f p w + g p w) := by
  refine ⟨fun w => (hf.base w).add (hg.base w), hf.fiber.add hg.fiber, ?_⟩
  intro d
  simpa only [fderiv_fun_add (hf.base _) (hg.base _), ContinuousLinearMap.add_apply] using
    (hf.slope d).add (hg.slope d)

private theorem RegularAt.neg {z : ℂ} {f : ℂ → ℂ → ℂ} (hf : RegularAt z f) :
    RegularAt z (fun p w => -f p w) := by
  refine ⟨fun w => (hf.base w).neg, hf.fiber.neg, ?_⟩
  intro d
  simp only [fderiv_fun_neg, ContinuousLinearMap.neg_apply]
  exact (hf.slope d).neg

private theorem RegularAt.mul {z : ℂ} {f g : ℂ → ℂ → ℂ} (hf : RegularAt z f) (hg : RegularAt z g) :
    RegularAt z (fun p w => f p w * g p w) := by
  refine ⟨fun w => (hf.base w).mul (hg.base w), hf.fiber.mul hg.fiber, ?_⟩
  intro d
  simp only [fderiv_fun_mul (hf.base _) (hg.base _), ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  exact (hf.fiber.mul (hg.slope d)).add (hg.fiber.mul (hf.slope d))

private theorem RegularAt.pow {z : ℂ} {f : ℂ → ℂ → ℂ} (hf : RegularAt z f) (n : ℕ) :
    RegularAt z (fun p w => f p w ^ n) := by
  induction n with
  | zero => simpa using (baseOnly z (fun _ => 1) (differentiableAt_const _))
  | succ n ih => simpa only [pow_succ] using ih.mul hf

private theorem primitive_regular (terms : List Term) (z : ℂ) :
    RegularAt z (primitive terms) := by
  have hc (c : ℂ) := baseOnly z (fun _ => c) (differentiableAt_const c)
  have hz := baseOnly z id (differentiableAt_id (𝕜 := ℝ))
  have hs := baseOnly z conj Complex.conjCLE.differentiable.differentiableAt
  have hw := velocityOnly z id (differentiable_id (𝕜 := ℂ))
  have hu : RegularAt z firstIntegral := by
    simpa only [firstIntegral, sub_eq_add_neg, id_eq] using hz.add (((hw.pow 2).mul hs).neg)
  induction terms with
  | nil => exact hc 0
  | cons m ts ih =>
    have hm := (((((hc m.c).mul (hu.pow m.p)).mul (hw.pow m.k)).mul
      (hc ((m.q + 1 : ℂ)⁻¹))).mul (hs.pow (m.q + 1)))
    simpa only [primitive, List.map_cons, List.sum_cons, Term.primitive, Term.coeff, div_eq_mul_inv,
      id_eq] using hm.add ih

variable {n : ℕ}

/-- The holomorphic continuation of `w A` in the velocity coordinate. -/
def diskCoefficient (a : UpperDisk.Coefficients n) (z w : ℂ) : UpperDisk.Mat n :=
  fun i j => BoundaryModes.numerator (upperTerms (UpperDisk.terms a) i j) z w

theorem diskCoefficient_trace (a : UpperDisk.Coefficients n) (z : ℂ) (w : Circle) :
    diskCoefficient a z w = (w : ℂ) • UpperDisk.field a z w := by
  ext i j
  have hu : (w : ℂ) * conj (w : ℂ) = 1 := by
    rw [← Circle.coe_inv_eq_conj, Circle.coe_inv, mul_inv_cancel₀ w.coe_ne_zero]
  simp only [diskCoefficient, Matrix.smul_apply, smul_eq_mul, UpperDisk.field_eq,
    BoundaryModes.attenuation_split, ← mul_assoc, hu, one_mul]

private theorem frame_regular (a : UpperDisk.Coefficients n) (z : ℂ) (i j : Fin n) :
    RegularAt z (fun p w => UpperDisk.frame a p w i j) :=
  (baseOnly z (fun _ => (1 : UpperDisk.Mat n) i j) (differentiableAt_const _)).add
    (primitive_regular (upperP (UpperDisk.terms a) i j) z).neg

/-- The actual horizontal frame equation on the full closed velocity disk,
for every entry of the arbitrary-rank triangular polynomial construction. -/
theorem frame_horizontal (a : UpperDisk.Coefficients n) (z : ℂ) {w : ℂ}
    (hw : w ∈ closedBall 0 1) (i j : Fin n) :
    residual (diskCoefficient a) (UpperDisk.frame a) z w i j = 0 := by
  apply transport_to_disk (A := fun p v => UpperDisk.field a p v) _ _ _
    (fun v k l => (frame_regular a z k l).base v) (diskCoefficient_trace a z) _ _ hw i j
  · intro v k l
    apply UpperDisk.geodesic_transport
    rw [← Circle.coe_inv_eq_conj, Circle.coe_inv, mul_inv_cancel₀ v.coe_ne_zero]
  · intro k l
    apply Differentiable.diffContOnCl
    have h := frame_regular a z k l
    have hprod : Differentiable ℂ
        (fun v => (diskCoefficient a z v * UpperDisk.frame a z v) k l) := by
      simp only [Matrix.mul_apply]
      apply Differentiable.fun_sum
      intro s _
      exact (BoundaryModes.numerator_entire _ z).mul (frame_regular a z s l).fiber
    have hplus := ((h.slope 1).div_const 2).add ((h.slope I).div_const (2 * I))
    have hminus := ((h.slope 1).div_const 2).sub ((h.slope I).div_const (2 * I))
    exact (((differentiable_id.pow 2).mul hplus).add hminus).add hprod

/-- Both components of the twistor holomorphic frame equation, along with
the everywhere-defined two-sided inverse, on the flat velocity disk. -/
theorem polynomial_twistor_frame (a : UpperDisk.Coefficients n) (z : ℂ) {w : ℂ}
    (hw : w ∈ closedBall 0 1) :
    UpperDisk.frame a z w * UpperDisk.inverseFrame a z w = 1 ∧
    UpperDisk.inverseFrame a z w * UpperDisk.frame a z w = 1 ∧
    ∀ i j, DifferentiableAt ℂ (fun v => UpperDisk.frame a z v i j) w ∧
      residual (diskCoefficient a) (UpperDisk.frame a) z w i j = 0 := by
  obtain ⟨hleft, hright⟩ := UpperDisk.inverse_identities a z w
  exact ⟨hleft, hright, fun i j => ⟨(frame_regular a z i j).fiber w, frame_horizontal a z hw i j⟩⟩

end TransportOkaGrauert.UpperTwistor
