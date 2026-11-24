import TransportOkaGrauert.SmoothLocalFlow
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecificLimits.Normed

/-! # Finite-time inversion of the linearized path equation
The simplex factor 1/n! yields a convergent operator series at arbitrary
finite times, without any uniform small-time assumption. -/
namespace TransportOkaGrauert.VolterraInverse
noncomputable section
open Set Filter Metric MeasureTheory SmoothLocalFlow
open scoped ContDiff Topology unitInterval
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def operator (A : Path (E →L[ℝ] E)) : Path E →L[ℝ] Path E :=
  (integration (E := E)).comp (SmoothPathComposition.evaluation (K := unitInterval) (E := E) (F := E) A)

omit [CompleteSpace E] in
set_option maxHeartbeats 500000 in
theorem iterated_bound (A : Path (E →L[ℝ] E)) (v : Path E) (n : ℕ) (s : unitInterval) :
    ‖(((operator A)^n) v) s‖ ≤ (‖A‖^n * ‖v‖ / (n.factorial:ℝ)) * (s:ℝ)^n := by
  induction n generalizing s with
  | zero => simpa using v.norm_coe_le_norm s
  | succ n ih =>
    rw [pow_succ']
    let V := ((operator A)^n) v
    let B := ‖A‖ * (‖A‖^n * ‖v‖ / (n.factorial:ℝ))
    change ‖∫ x : ℝ in 0..s.val, A (projIcc 0 1 zero_le_one x) (V (projIcc 0 1 zero_le_one x))‖ ≤ _
    calc
      _ ≤ ∫ x : ℝ in 0..s.val, B * x^n := by
        apply intervalIntegral.norm_integral_le_of_norm_le s.property.1 _ (by
          apply Continuous.intervalIntegrable; fun_prop)
        apply Filter.Eventually.of_forall
        intro x hx
        have hx1 : x ∈ Icc (0:ℝ) 1 := ⟨hx.1.le,hx.2.trans s.property.2⟩
        let t : unitInterval := ⟨x,hx1⟩
        rw [projIcc_of_mem _ hx1]
        calc
          ‖A t (V t)‖ ≤ ‖A‖ * ‖V t‖ := ((A t).le_opNorm _).trans
            (mul_le_mul_of_nonneg_right (A.norm_coe_le_norm t) (norm_nonneg _))
          _ ≤ _ := by
            rw [show B*x^n = ‖A‖*((‖A‖^n*‖v‖/(n.factorial:ℝ))*t.val^n) by dsimp [B,t];ring]
            exact mul_le_mul_of_nonneg_left (ih t) (norm_nonneg A)
      _ = _ := by
        rw [intervalIntegral.integral_const_mul, integral_pow,zero_pow (by omega : n+1 ≠ 0),sub_zero]
        simp only [B,Nat.factorial_succ,Nat.cast_mul,Nat.cast_succ,pow_succ]
        have hn : (n.factorial : ℝ) ≠ 0 := by positivity
        have hk : (n:ℝ)+1 ≠ 0 := by positivity
        field_simp [hn,hk]

omit [CompleteSpace E] in
private theorem op_bound (A : Path (E →L[ℝ] E)) (n : ℕ) :
    ‖(operator A)^n‖ ≤ ‖A‖^n/(n.factorial:ℝ) := by
  have hn : 0 ≤ ‖A‖^n/(n.factorial:ℝ) := by positivity
  apply ContinuousLinearMap.opNorm_le_bound ((operator A)^n) hn
  intro v
  apply (ContinuousMap.norm_le (((operator A)^n) v) (mul_nonneg hn (norm_nonneg v))).mpr
  intro s
  have hp : (s:ℝ)^n ≤ 1 := pow_le_one₀ s.property.1 s.property.2
  calc
    _ ≤ (‖A‖^n * ‖v‖ / (n.factorial:ℝ)) * (s:ℝ)^n := iterated_bound A v n s
    _ ≤ ‖A‖^n*‖v‖/(n.factorial:ℝ) := mul_le_of_le_one_right (by positivity) hp
    _ = _ := by ring

theorem bijective (A : Path (E →L[ℝ] E)) :
    Function.Bijective ((1 - operator A : Path E →L[ℝ] Path E) : Path E → Path E) := by
  let B := operator A
  have sm : Summable (fun n : ℕ => B^n) :=
    Summable.of_norm_bounded (f := fun n : ℕ => B^n) (g := fun n : ℕ => ‖A‖^n/(n.factorial:ℝ))
      (Real.summable_pow_div_factorial ‖A‖) (op_bound A)
  letI : IsTopologicalRing (Path E →L[ℝ] Path E) :=
    @NonUnitalSeminormedRing.toIsTopologicalRing _ (@SeminormedRing.toNonUnitalSeminormedRing _ (@NormedRing.toSeminormedRing _ (ContinuousLinearMap.toNormedRing)))
  let C : Path E →L[ℝ] Path E := ∑' n : ℕ, B^n
  have right : (1-B)*C = 1 := sm.one_sub_mul_tsum_pow
  have left : C*(1-B) = 1 := sm.tsum_pow_mul_one_sub
  exact ⟨Function.LeftInverse.injective (f := (1-B : Path E →L[ℝ] Path E))
      (g := (C : Path E → Path E)) (fun x => DFunLike.congr_fun left x),
    Function.RightInverse.surjective (f := (1-B : Path E →L[ℝ] Path E))
      (g := (C : Path E → Path E)) (fun x => DFunLike.congr_fun right x)⟩

end
end TransportOkaGrauert.VolterraInverse
