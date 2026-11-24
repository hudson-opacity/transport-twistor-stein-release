import TransportOkaGrauert.SimpleDiskTarget
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Tactic

/-! The Euclidean unit disk satisfies the geometric simplicity hypotheses.
Straight lines leave the closed disk in both time directions, while the
scalar Jacobi equation reduces to a function with vanishing second derivative. -/

namespace TransportOkaGrauert.FlatSimple

open Complex Metric Set SimpleDiskTarget
open scoped ContDiff

/-- On a nondegenerate compact interval, a solution to the flat scalar Jacobi
equation has constant slope. Two zero endpoint values force that slope to vanish. -/
private theorem zeroJacobi {a b : ℝ} (hab : a < b) {j dj : ℝ → ℝ}
    (hj : ∀ t ∈ Icc a b, HasDerivWithinAt j (dj t) (Icc a b) t)
    (hdj : ∀ t ∈ Icc a b, HasDerivWithinAt dj 0 (Icc a b) t)
    (ja : j a = 0) (jb : j b = 0) : ∀ t ∈ Icc a b, j t = 0 := by
  have constant := constant_of_has_deriv_right_zero
    (fun t ht => (hdj t ht).continuousWithinAt)
    (fun t ht => (hdj t (mem_Icc_of_Ico ht)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht))
  let line (t : ℝ) := (t - a) * dj a
  have line' (t : ℝ) : HasDerivAt line (dj a) t := by
    simpa only [line, one_mul] using ((hasDerivAt_id' t).sub_const a).mul_const (dj a)
  have affine : ∀ t ∈ Icc a b, j t = line t := by
    apply eq_of_has_deriv_right_eq (f' := fun _ => dj a)
    · intro t ht
      have h := hj t (mem_Icc_of_Ico ht)
      rw [constant t (mem_Icc_of_Ico ht)] at h
      exact h.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)
    · exact fun t _ => (line' t).hasDerivWithinAt
    · exact fun t ht => (hj t ht).continuousWithinAt
    · exact fun t _ => (line' t).continuousAt.continuousWithinAt
    · simp [line, ja]
  have at_b := affine b (right_mem_Icc.mpr hab.le)
  have slopeZero : dj a = 0 :=
    (mul_eq_zero.mp (by simpa [line, jb] using at_b.symm : (b - a) * dj a = 0)).resolve_left
      (sub_ne_zero.mpr hab.ne')
  intro t ht
  simpa [line, slopeZero] using affine t ht

/-- The flat geodesic equations force the angle to stay fixed and the position
to be affine, including at the endpoints of a closed geodesic segment. -/
private theorem affine_of_flat_equations {a b : ℝ} {z : ℝ → ℂ} {θ : ℝ → ℝ}
    (hz : ∀ t ∈ Icc a b, HasDerivWithinAt z (Circle.exp (θ t) : ℂ) (Icc a b) t)
    (hθ : ∀ t ∈ Icc a b, HasDerivWithinAt θ 0 (Icc a b) t) :
    ∀ t ∈ Icc a b, z t = z a + ((t - a : ℝ) : ℂ) * (Circle.exp (θ a) : ℂ) := by
  have constant := constant_of_has_deriv_right_zero
    (fun t ht => (hθ t ht).continuousWithinAt)
    (fun t ht => (hθ t (mem_Icc_of_Ico ht)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht))
  let line (t : ℝ) := z a + ((t - a : ℝ) : ℂ) * (Circle.exp (θ a) : ℂ)
  have line' (t : ℝ) : HasDerivAt line (Circle.exp (θ a) : ℂ) t := by
    simpa only [line, Complex.ofReal_sub, Complex.ofRealCLM_apply, Complex.ofReal_one, one_mul] using
      ((((Complex.ofRealCLM.hasDerivAt (x := t)).sub_const (a : ℂ)).mul_const
        (Circle.exp (θ a) : ℂ)).const_add (z a))
  apply eq_of_has_deriv_right_eq (g := line) (f' := fun _ => (Circle.exp (θ a) : ℂ))
  · intro t ht
    have h := hz t (mem_Icc_of_Ico ht)
    rw [constant t (mem_Icc_of_Ico ht)] at h
    exact h.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)
  · exact fun t _ => (line' t).hasDerivWithinAt
  · exact fun t ht => (hz t ht).continuousWithinAt
  · exact fun t _ => (line' t).continuousAt.continuousWithinAt
  · simp [line]

/-- A straight line from the closed unit disk with unit speed is outside the
disk after three units of elapsed time, forward or backward. -/
private theorem line_escapes (z : ℂ) (hz : z ∈ closedBall 0 1) (w : Circle) (t : ℝ)
    (ht : |t| = 3) : 1 < ‖z + (t : ℂ) * w‖ := by
  have h := norm_sub_le (z + (t : ℂ) * w) z
  rw [add_sub_cancel_left, norm_mul, Circle.norm_coe, mul_one, Complex.norm_real,
    Real.norm_eq_abs, ht] at h
  have hz' : ‖z‖ ≤ 1 := mem_closedBall_zero_iff.mp hz
  linarith

/-- Every Euclidean unit geodesic whose endpoints lie in the disk has travel
time at most its Euclidean diameter. -/
theorem chord_time_le_two {a b : ℝ} (hab : a ≤ b) {z : ℝ → ℂ} {θ : ℝ → ℝ}
    (geodesic : unitGeodesicOn (fun _ => 0) z θ (Icc a b))
    (ha : z a ∈ closedBall 0 1) (hb : z b ∈ closedBall 0 1) : b - a ≤ 2 := by
  have flat := affine_of_flat_equations (z := z) (θ := θ)
    (fun t ht => by simpa using (geodesic t ht).1)
    (fun t ht => by simpa [Isothermal.angularDrift] using (geodesic t ht).2)
    b (right_mem_Icc.mpr hab)
  have chord : z b - z a = ((b - a : ℝ) : ℂ) * (Circle.exp (θ a) : ℂ) := by
    rw [flat, add_sub_cancel_left]
  have bound := norm_sub_le (z b) (z a)
  rw [chord, norm_mul, Circle.norm_coe, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr hab)] at bound
  have ha' := mem_closedBall_zero_iff.mp ha
  have hb' := mem_closedBall_zero_iff.mp hb
  linarith

/-- The constant zero conformal factor gives a simple metric in the concrete
chart used by the integrating-factor target. -/
theorem euclidean_simple : SimpleMetric (fun _ : ℂ => (0 : ℝ)) where
  smooth := contDiff_const
  strictConvex := by simp
  escapes := by
    intro z₀ hz₀ θ₀
    let w : Circle := Circle.exp θ₀
    let z (t : ℝ) := z₀ + (t : ℂ) * w
    refine ⟨-3, 3, z, fun _ => θ₀, by norm_num, by norm_num, by simp [z], rfl, ?_,
      line_escapes z₀ hz₀ w (-3) (by norm_num), line_escapes z₀ hz₀ w 3 (by norm_num)⟩
    intro t ht
    constructor
    · have h : HasDerivAt z (w : ℂ) t := by
        simpa [z] using ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const (w : ℂ)).const_add z₀
      simpa [w] using h.hasDerivWithinAt (s := Icc (-3) 3)
    · simpa [Isothermal.angularDrift] using hasDerivWithinAt_const t (Icc (-3) 3) θ₀
  noConjugate := by
    intro a b hab z θ _ _ j dj hJac ja jb
    apply zeroJacobi hab (fun t ht => (hJac t ht).1) _ ja jb
    intro t ht
    simpa [curvature, laplacian] using (hJac t ht).2

end TransportOkaGrauert.FlatSimple
