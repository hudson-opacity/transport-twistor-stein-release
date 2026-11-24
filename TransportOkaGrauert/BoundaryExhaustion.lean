import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

/-!
# Boundary concentration of reciprocal divisors

Along an arclength arc, a family of nonvanishing divisors with a uniform
first-order growth bound contributes a divergent reciprocal-square integral
when its value at the initial endpoint tends to zero. The estimate uses
only the first subarc of length equal to the endpoint modulus.
-/

namespace TransportOkaGrauert.BoundaryExhaustion

open Filter MeasureTheory Set
open scoped Topology

/-- If an arc begins with modulus at most `δ` and grows with slope at most
`C`, its reciprocal-square integral is at least `1 / ((1+C)² δ)`. -/
theorem arc_lower_bound {F : ℝ → ℂ} {C δ ε : ℝ}
    (hC : 0 ≤ C) (hδ : 0 < δ) (hδε : δ ≤ ε)
    (hF : ContinuousOn F (Icc 0 ε))
    (hn : ∀ t ∈ Icc 0 ε, F t ≠ 0)
    (hg : ∀ t ∈ Icc 0 ε, ‖F t‖ ≤ δ + C * t) :
    ((1 + C) ^ 2 * δ)⁻¹ ≤ ∫ t in (0 : ℝ)..ε, (‖F t‖ ^ 2)⁻¹ := by
  have hsub : Icc 0 δ ⊆ Icc 0 ε := Icc_subset_Icc_right hδε
  have hc : ContinuousOn (fun t => (‖F t‖ ^ 2)⁻¹) (Icc 0 ε) :=
    (hF.norm.pow 2).inv₀ fun t ht => pow_ne_zero _ (norm_ne_zero_iff.mpr (hn t ht))
  calc
    ((1 + C) ^ 2 * δ)⁻¹ = ∫ _ in (0 : ℝ)..δ, (((1 + C) * δ) ^ 2)⁻¹ := by
      rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
      field_simp
    _ ≤ ∫ t in (0 : ℝ)..δ, (‖F t‖ ^ 2)⁻¹ := by
      apply intervalIntegral.integral_mono_on hδ.le intervalIntegrable_const
        ((hc.mono hsub).intervalIntegrable_of_Icc hδ.le)
      intro t ht
      have hbound : ‖F t‖ ≤ (1 + C) * δ := calc
        ‖F t‖ ≤ δ + C * t := hg t (hsub ht)
        _ ≤ δ + C * δ := by gcongr; exact ht.2
        _ = (1 + C) * δ := by ring
      exact inv_anti₀ (pow_pos (norm_pos_iff.mpr (hn t (hsub ht))) 2)
        (pow_le_pow_left₀ (norm_nonneg _) hbound 2)
    _ ≤ ∫ t in (0 : ℝ)..ε, (‖F t‖ ^ 2)⁻¹ := by
      exact intervalIntegral.integral_mono_interval le_rfl hδ.le hδε
        (.of_forall fun t => inv_nonneg.mpr (sq_nonneg _))
        (hc.intervalIntegrable_of_Icc (hδ.le.trans hδε))

/-- The integrals diverge along any family for which the endpoint value tends
to zero and the linear growth bound along the arc is uniform in the family. -/
theorem tendsto_arc_integral_atTop {α : Type*} {l : Filter α}
    {F : α → ℝ → ℂ} {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε)
    (hF : ∀ i, ContinuousOn (F i) (Icc 0 ε))
    (hn : ∀ i t, t ∈ Icc 0 ε → F i t ≠ 0)
    (hg : ∀ i t, t ∈ Icc 0 ε → ‖F i t‖ ≤ ‖F i 0‖ + C * t)
    (hvanish : Tendsto (fun i => F i 0) l (𝓝 0)) :
    Tendsto (fun i => ∫ t in (0 : ℝ)..ε, (‖F i t‖ ^ 2)⁻¹) l atTop := by
  have hzero : Tendsto (fun i => ‖F i 0‖) l (𝓝 0) := by simpa using hvanish.norm
  have hpos (i : α) : 0 < ‖F i 0‖ := norm_pos_iff.mpr (hn i 0 ⟨le_rfl, hε.le⟩)
  have hcoef : 0 < (1 + C) ^ 2 := by positivity
  have hscale : Tendsto (fun i => (1 + C) ^ 2 * ‖F i 0‖) l (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, .of_forall fun i => mul_pos hcoef (hpos i)⟩
    simpa using (tendsto_const_nhds (x := (1 + C) ^ 2)).mul hzero
  apply tendsto_atTop_mono' l _ (tendsto_inv_nhdsGT_zero.comp hscale)
  filter_upwards [hzero.eventually_lt_const hε] with i hi
  exact arc_lower_bound hC (hpos i) hi.le (hF i) (hn i) (hg i)

end TransportOkaGrauert.BoundaryExhaustion
