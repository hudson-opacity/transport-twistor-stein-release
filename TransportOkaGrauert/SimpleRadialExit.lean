import TransportOkaGrauert.GeodesicEndpoint
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! # Transverse first exit for the chart geodesic equation

The disk is defined by its Euclidean radius. Along a unit geodesic its
outward normal velocity has derivative strictly positive at a tangency,
by the strict-convexity clause of the chart definition of simplicity.
Consequently a first hit from the interior has strictly outward velocity.
-/

noncomputable section
namespace TransportOkaGrauert.SimpleRadialExit

open Complex Set Metric Filter SimpleDiskTarget
open scoped ContDiff ComplexConjugate Topology

/-- The radial component of the unit Euclidean direction, multiplied by the base radius. -/
def normal (z : ℂ) (w : Circle) : ℝ := (z * conj (w : ℂ)).re

private theorem circle_unit (w : Circle) : (w : ℂ) * conj (w : ℂ) = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp

private theorem angle_deriv (s : ℝ) :
    HasDerivAt (fun u : ℝ => (Circle.exp u : ℂ)) (I * (Circle.exp s : ℂ)) s := by
  simpa [Circle.coe_exp, mul_comm] using (((Complex.ofRealCLM.hasDerivAt (x := s)).mul_const I).cexp)

private theorem tangent_drift {σ : ℂ → ℝ} {z : ℂ} {w : Circle} (h : normal z w = 0) :
    Isothermal.angularDrift σ z w * (z * conj (w : ℂ)).im = fderiv ℝ σ z z := by
  let B := (z * conj (w : ℂ)).im
  have hz : z = B • (I * (w : ℂ)) := by
    have ht : z * conj (w : ℂ) = B * I := by
      apply Complex.ext
      · simpa only [Complex.mul_I_re, Complex.ofReal_im, neg_zero] using h
      · simp only [B, Complex.mul_I_im, Complex.ofReal_re]
    calc
      z = (z * conj (w : ℂ)) * (w : ℂ) := by
        rw [mul_assoc, mul_comm (conj (w : ℂ)), circle_unit, mul_one]
      _ = _ := by rw [ht, Complex.real_smul, mul_assoc]
  have hi : I * (w : ℂ) = (-(w : ℂ).im) • (1 : ℂ) + (w : ℂ).re • I := by
    apply Complex.ext <;> simp [Complex.real_smul]
  change Isothermal.angularDrift σ z w * B = _
  conv_rhs => arg 2; rw [hz, hi]
  rw [map_smul, map_add, map_smul, map_smul]
  simp only [Isothermal.angularDrift, smul_eq_mul]
  ring

theorem radiusSq_deriv {σ z θ S} (ray : unitGeodesicOn σ z θ S)
    {t : ℝ} (ht : S ∈ 𝓝 t) :
    HasDerivAt (fun s => Complex.normSq (z s))
      (2 * Real.exp (-σ (z t)) * normal (z t) (Circle.exp (θ t))) t := by
  have dz := ((ray t (mem_of_mem_nhds ht)).1).hasDerivAt ht
  have dx := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t dz
  have dy := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t dz
  convert (dx.mul dx).add (dy.mul dy) using 1
  generalize Real.exp (-σ (z t)) = e
  simp [normal, Complex.mul_re, Complex.mul_im]
  ring

/-- At a boundary tangency the derivative of the outward component is the
conformal speed times the (scaled) strict-boundary-curvature expression. -/
theorem normal_deriv_at_tangent {σ z θ S} (ray : unitGeodesicOn σ z θ S)
    {t : ℝ} (ht : S ∈ 𝓝 t) (tan : normal (z t) (Circle.exp (θ t)) = 0) :
    HasDerivAt (fun s => normal (z s) (Circle.exp (θ s)))
      (Real.exp (-σ (z t)) * (1 + fderiv ℝ σ (z t) (z t))) t := by
  have dz := ((ray t (mem_of_mem_nhds ht)).1).hasDerivAt ht
  have da := ((ray t (mem_of_mem_nhds ht)).2).hasDerivAt ht
  have dw := (angle_deriv (θ t)).scomp t da
  have dc := Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t dw
  have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (dz.mul dc)
  let w := Circle.exp (θ t)
  let c := Real.exp (-σ (z t))
  let d := Isothermal.angularDrift σ (z t) w
  change HasDerivAt _ (((c : ℂ) * w * conj (w : ℂ) +
    z t * conj ((c*d : ℝ) • (I * (w : ℂ)))).re) t at h
  convert h using 1
  change c * (1 + fderiv ℝ σ (z t) (z t)) = _
  rw [mul_assoc (c : ℂ), circle_unit, mul_one, ← tangent_drift tan]
  simp [Complex.real_smul, Complex.mul_re, Complex.mul_im, d, w]
  ring

private theorem negative_before {f : ℝ → ℝ} {T v : ℝ} (df : HasDerivAt f v T)
    (hzero : f T = 0) (hv : 0 < v) : ∀ᶠ t in 𝓝[<] T, f t < 0 := by
  have hs := (hasDerivAt_iff_tendsto_slope_left_right.mp df).1.eventually (Ioi_mem_nhds hv)
  filter_upwards [hs, self_mem_nhdsWithin] with t h ht
  change t < T at ht
  change 0 < slope f T t at h
  rw [slope_def_field, hzero, sub_zero] at h
  exact ((div_pos_iff.mp h).resolve_left (fun u => (not_lt_of_ge ht.le) (sub_pos.mp u.2))).1

/-- An in-disk segment ending on the boundary has strictly outward direction
whenever it approaches the boundary from strictly inside. The given geodesic
continues past the hit, as supplied by the escape hypothesis. -/
theorem transverse_hit {σ z θ a b T} (simple : SimpleMetric σ)
    (ray : unitGeodesicOn σ z θ (Icc a b)) (ha : a ≤ 0) (hT : 0 < T) (hb : T < b)
    (hboundary : ‖z T‖ = 1) (inside : ∀ t ∈ Ico 0 T, ‖z t‖ < 1) :
    0 < normal (z T) (Circle.exp (θ T)) := by
  let N := fun t => normal (z t) (Circle.exp (θ t))
  have nearT := Icc_mem_nhds (ha.trans_lt hT) hb
  have rayT := ray T (show T ∈ Icc a b from ⟨(ha.trans_lt hT).le, hb.le⟩)
  have hcont : ContinuousAt N T := by
    apply Complex.continuous_re.continuousAt.comp
    apply (rayT.1.hasDerivAt nearT).continuousAt.mul
    exact Complex.continuous_conj.continuousAt.comp
      ((continuous_subtype_val.comp Circle.exp.continuous).continuousAt.comp
        (rayT.2.hasDerivAt nearT).continuousAt)
  by_contra! hn
  have hneg : ∀ᶠ t in 𝓝[<] T, N t < 0 := by
    rcases lt_or_eq_of_le hn with h | h
    · exact (hcont.eventually (Iio_mem_nhds h)).filter_mono nhdsWithin_le_nhds
    · exact negative_before (normal_deriv_at_tangent ray nearT h) h
        (mul_pos (Real.exp_pos _) (simple.strictConvex _ (mem_sphere_zero_iff_norm.mpr hboundary)))
  obtain ⟨u, hu, hU⟩ := (mem_nhdsLT_iff_exists_mem_Ico_Ioo_subset hT).mp hneg
  have sub : Icc u T ⊆ Icc a b := Icc_subset_Icc (ha.trans hu.1) hb.le
  have hc : ContinuousOn (fun t => Complex.normSq (z t)) (Icc u T) :=
    Complex.continuous_normSq.comp_continuousOn (fun t ht => ((ray t (sub ht)).1.continuousWithinAt).mono sub)
  obtain ⟨s, hs, eq⟩ := exists_hasDerivAt_eq_slope _ _ hu.2 hc (fun t ht =>
    radiusSq_deriv ray (Icc_mem_nhds ((ha.trans hu.1).trans_lt ht.1) (ht.2.trans hb)))
  have hpos : 0 < (Complex.normSq (z T) - Complex.normSq (z u)) / (T-u) := by
    apply div_pos _ (sub_pos.mpr hu.2)
    rw [sub_pos, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, hboundary, one_pow]
    nlinarith [inside u ⟨hu.1, hu.2⟩, norm_nonneg (z u)]
  exact (not_lt_of_ge ((mul_neg_of_pos_of_neg (mul_pos (by norm_num) (Real.exp_pos _)) (hU hs)).le))
    (eq.symm ▸ hpos)

/-- Every initial unit direction over an interior point admits a geodesic
to a first boundary hit with strictly outward normal velocity. -/
theorem exists_transverse_exit {σ : ℂ → ℝ} (simple : SimpleMetric σ) {z₀ : ℂ}
    (hz : z₀ ∈ ball 0 1) (θ₀ : ℝ) :
    ∃ a b T : ℝ, ∃ z θ, a < 0 ∧ 0 < T ∧ T < b ∧ z 0 = z₀ ∧ θ 0 = θ₀ ∧
      unitGeodesicOn σ z θ (Icc a b) ∧ ‖z T‖ = 1 ∧
      (∀ t ∈ Ico 0 T, ‖z t‖ < 1) ∧ 0 < normal (z T) (Circle.exp (θ T)) := by
  obtain ⟨a,b,z,θ,ha,hb,hz₀,hθ,ray,_,hout⟩ := simple.escapes _ (ball_subset_closedBall hz) θ₀
  have hstart : ‖z 0‖ < 1 := hz₀ ▸ mem_ball_zero_iff.mp hz
  have sub : Icc 0 b ⊆ Icc a b := Icc_subset_Icc_left ha.le
  have cz : ContinuousOn z (Icc 0 b) := fun t ht => ((ray t (sub ht)).1.continuousWithinAt).mono sub
  obtain ⟨T,hT,hbd,inside⟩ := GeodesicEndpoint.first_exit hb.le cz hstart hout.le
  have hp : 0 < T := lt_of_le_of_ne hT.1 (by rintro rfl; linarith)
  have he : T < b := lt_of_le_of_ne hT.2 (by rintro rfl; linarith)
  exact ⟨a,b,T,z,θ,ha,hp,he,hz₀,hθ,ray,hbd,inside,transverse_hit simple ray ha.le hp he hbd inside⟩

end TransportOkaGrauert.SimpleRadialExit
