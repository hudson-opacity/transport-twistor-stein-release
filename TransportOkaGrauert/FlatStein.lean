import TransportOkaGrauert.ChartStein

/-!
# Direct verification of all three Stein axioms on the flat transport disk

This is the constant conformal factor specialization of the fixed-chart
statement. The proof works above every open base subset of the unit disk.
-/
namespace TransportOkaGrauert.FlatStein
noncomputable section
open ChartStein Set Complex Metric
open scoped ContDiff ComplexConjugate

def divisor (a : ℂ) (p : E) : ℂ := FlatScalar.firstIntegral (p.1-a) p.2

private abbrev baseProj := ContinuousLinearMap.fst ℝ ℂ ℂ
private abbrev velProj := ContinuousLinearMap.snd ℝ ℂ ℂ

private def divisorSlope (a : ℂ) (p : E) : E →L[ℝ] ℂ :=
  baseProj - (p.2 ^ 2 • (Complex.conjCLE.toContinuousLinearMap.comp baseProj) +
    conj (p.1 - a) • ((2 • p.2 ^ (2 - 1 : ℕ)) • velProj))

private theorem divisor_derivative (a : ℂ) (p : E) :
    HasFDerivAt (divisor a) (divisorSlope a p) p := by
  have hz := (hasFDerivAt_fst (𝕜 := ℝ) (p := p)).sub_const a
  have hc := Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp p hz
  exact hz.sub (((hasFDerivAt_snd (𝕜 := ℝ) (p := p)).pow 2).mul hc)

private theorem slope_apply (a : ℂ) (p v : E) :
    divisorSlope a p v = v.1 - (p.2^2 * conj v.1 + conj (p.1-a) * (2*p.2*v.2)) := by
  simp [divisorSlope, smul_eq_mul, two_smul]
  ring_nf; simp

private theorem divisor_smooth (a : ℂ) : ContDiff ℝ ∞ (divisor a) := by
  have hc : ContDiff ℝ ∞ (fun p : E => conj (p.1-a)) :=
    Complex.conjCLE.contDiff.comp (contDiff_fst.sub contDiff_const)
  exact (contDiff_fst.sub contDiff_const).sub ((contDiff_snd.pow 2).mul hc)

private theorem divisor_hol (k : ℝ) (a : ℂ) (p : E) :
    HolAt (fun _ => k) (divisor a) p := by
  refine ⟨(divisor_smooth a).contDiffAt, ?_⟩
  unfold SatisfiesCR
  rw [(divisor_derivative a p).fderiv]
  constructor
  · simp [slope_apply]; ring
  · simp [slope_apply, connectionCoefficient]; ring_nf; simp [Complex.I_sq]

private theorem vel_hol (k : ℝ) (a : ℂ) (p : E) :
    HolAt (fun _ => k) (fun q => q.2-a) p := by
  refine ⟨(contDiff_snd.sub contDiff_const).contDiffAt, ?_⟩
  unfold SatisfiesCR
  rw [((hasFDerivAt_snd (𝕜 := ℝ) (p := p)).sub_const a).fderiv]
  simp [connectionCoefficient]

private theorem vel_id_hol (k : ℝ) (p : E) : HolAt (fun _ => k) Prod.snd p := by
  simpa using vel_hol k 0 p

private theorem divisor_coordinates {p : E} (hw : ‖p.2‖ < 1) :
    Function.Bijective (fderiv ℝ (fun q : E => (divisor p.1 q, q.2)) p) := by
  rw [((divisor_derivative p.1 p).prodMk (hasFDerivAt_snd (𝕜 := ℝ))).fderiv]
  let L := (divisorSlope p.1 p).prod velProj
  change Function.Bijective L
  have hinj : Function.Injective L := by
    apply (LinearMap.ker_eq_bot.mp ?_ : Function.Injective L.toLinearMap)
    apply LinearMap.ker_eq_bot'.mpr
    intro v h
    have hvel : v.2 = 0 := congrArg Prod.snd h
    have hbase := congrArg Prod.fst h
    change divisorSlope p.1 p v = 0 at hbase
    rw [slope_apply] at hbase
    simp only [sub_self, map_zero, zero_mul, add_zero] at hbase
    have hv := (SteinDivisor.firstIntegral_interior_zero_iff v.1 p.2 hw).mp hbase
    exact Prod.ext hv hvel
  exact ⟨hinj, LinearMap.injective_iff_surjective.mp (show Function.Injective L.toLinearMap from hinj)⟩

/-- All three holomorphic Stein axioms for every constant conformal factor,
including compactness for the hull taken over *all* CR-holomorphic tests.
No abstract integrating factors, geometric existence axioms, or assumed
Stein criteria are used. -/
theorem constant_conformal_factor (k : ℝ) (U : Set ℂ) (_hU : IsOpen U)
    (_hsub : U ⊆ ball 0 1) : HasSteinProperties (fun _ => k) U := by
  constructor
  · intro K hK
    letI : CompactSpace ClosedDisk := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
    apply DivisorHull.isCompact_testHull_of_boundary_divisors
      (fun _ h => continuous_tests h) _ hK
    intro p hout
    by_cases hbase : p.1.val ∈ U
    · have hr : ¬ ‖p.2.val‖ < 1 := fun hr => hout ⟨hbase, hr⟩
      let f : E → ℂ := fun q => q.2 - p.2.val
      have nz (u : interiorOver U) : f (point u.val) ≠ 0 := by
        intro h
        have he := sub_eq_zero.mp h
        exact hr (he ▸ u.property.2)
      refine ⟨f ∘ point, (continuous_snd.sub continuous_const).comp continuous_point,
        sub_self _, nz, ?_⟩
      exact ⟨fun q => (f q)⁻¹, fun u => (vel_hol k _ _).inv (nz u), fun _ => rfl⟩
    · let f := divisor p.1.val
      have nz (u : interiorOver U) : f (point u.val) ≠ 0 := by
        intro h
        have he := (SteinDivisor.firstIntegral_interior_zero_iff _ _ u.property.2).mp h
        exact hbase ((sub_eq_zero.mp he) ▸ u.property.1)
      refine ⟨f ∘ point, (divisor_smooth _).continuous.comp continuous_point, ?_, nz, ?_⟩
      · simp [f, divisor, point, FlatScalar.firstIntegral]
      · exact ⟨fun q => (f q)⁻¹, fun u => (divisor_hol k _ _).inv (nz u), fun _ => rfl⟩
  · intro p q hne
    by_cases hb : p.val.1.val = q.val.1.val
    · refine ⟨Prod.snd, fun _ => vel_id_hol k _, ?_⟩
      intro h
      exact hne (Subtype.ext (Prod.ext (Subtype.ext hb) (Subtype.ext h)))
    · refine ⟨divisor p.val.1.val, fun _ => divisor_hol k _ _, ?_⟩
      intro h
      have hp : divisor p.val.1.val (point p.val) = 0 := by
        simp [divisor, point, FlatScalar.firstIntegral]
      have eq := (SteinDivisor.firstIntegral_interior_zero_iff _ _ q.property.2).mp (h ▸ hp)
      exact hb (sub_eq_zero.mp eq).symm
  · intro p
    exact ⟨divisor p.val.1.val, Prod.snd, fun _ => divisor_hol k _ _,
      fun _ => vel_id_hol k _, divisor_coordinates (p := point p.val) p.property.2⟩

end
end TransportOkaGrauert.FlatStein
