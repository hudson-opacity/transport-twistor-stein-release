import TransportOkaGrauert.ScalarGeneralKernelBlowup
import Mathlib.Topology.MetricSpace.Thickening

/-! # A smooth remainder after subtracting the screened Riesz kernel -/

noncomputable section
namespace TransportOkaGrauert.ScalarGeneralKernel
open Complex Metric Set Filter MeasureTheory
open scoped ContDiff Topology

abbrev RadialParameter := (ℂ × ℝ) × ℂ

/-- Hadamard division in the radial parameter. The auxiliary base and
direction parameters may be differentiated arbitrarily often. -/
private theorem radial_division {F : RadialParameter → ℝ} (sF : ContDiff ℝ ∞ F) :
    ∃ R : RadialParameter → ℝ, ContDiff ℝ ∞ R ∧
      ∀ a r v, r * R ((a,r),v) = F ((a,r),v) - F ((a,0),v) := by
  let P (q : RadialParameter × ℝ) : RadialParameter := ((q.1.1.1,q.2*q.1.1.2),q.1.2)
  let e : RadialParameter := ((0,1),0)
  let R (p : RadialParameter) := ∫ t in (0:ℝ)..1, fderiv ℝ F (P (p,t)) e
  have sP : ContDiff ℝ ∞ P := ((contDiff_fst.comp (contDiff_fst.comp contDiff_fst)).prodMk
    (contDiff_snd.mul (contDiff_snd.comp (contDiff_fst.comp contDiff_fst)))).prodMk (contDiff_snd.comp contDiff_fst)
  have sR : ContDiff ℝ ∞ R := ScalarGeneralCauchy.integral_smooth (g := fun q => fderiv ℝ F (P q) e)
    (((sF.fderiv_right (m := ∞) (by simp)).comp sP).clm_apply contDiff_const) one_pos
  refine ⟨R,sR,fun a r v => ?_⟩
  let line (t : ℝ) : RadialParameter := ((a,t*r),v)
  have dl (t : ℝ) : HasDerivAt line (r • e) t := by
    simpa [e] using (((hasDerivAt_const t a).prodMk ((hasDerivAt_id t).mul_const r)).prodMk (hasDerivAt_const t v))
  have d (t : ℝ) : HasDerivAt (F ∘ line) (r * fderiv ℝ F (P (((a,r),v),t)) e) t := by
    simpa only [map_smul, smul_eq_mul] using (sF.differentiable (by simp) (line t)).hasFDerivAt.comp_hasDerivAt t (dl t)
  have sl : ContDiff ℝ ∞ (F ∘ line) := sF.comp ((contDiff_const.prodMk (contDiff_id.mul contDiff_const)).prodMk contDiff_const)
  have eq := intervalIntegral.integral_deriv_eq_sub (a := 0) (b := 1) (f := F ∘ line)
    (fun t _ => (d t).differentiableAt) ((sl.continuous_deriv (by simp)).intervalIntegrable _ _)
  simp_rw [(d _).deriv] at eq
  simpa [R,line,intervalIntegral.integral_const_mul] using eq

private theorem uniform_radius {K : Set ℂ} (hK : IsCompact K) {good : Set RadialParameter}
    (hg : ∀ a ∈ K, ∀ v : ℂ, ‖v‖ = 1 → good ∈ 𝓝 ((a,0),v)) :
    ∃ δ > 0, ∀ a ∈ K, ∀ v : ℂ, ‖v‖ = 1 → ∀ r : ℝ, 0 < r → r < δ → ((a,r),v) ∈ good := by
  let face : Set RadialParameter := (K ×ˢ ({0} : Set ℝ)) ×ˢ sphere (0:ℂ) 1
  have compact : IsCompact face := (hK.prod isCompact_singleton).prod (isCompact_sphere _ _)
  have inOpen : face ⊆ interior good := by
    rintro ⟨⟨a,r⟩,v⟩ ⟨⟨ha,hr⟩,hv⟩
    obtain rfl : r = 0 := hr
    exact mem_interior_iff_mem_nhds.mpr (hg a ha v (mem_sphere_zero_iff_norm.mp hv))
  obtain ⟨δ,hδ,sub⟩ := compact.exists_thickening_subset_open isOpen_interior inOpen
  refine ⟨δ,hδ,fun a ha v hv r hr h => interior_subset (sub (mem_thickening_iff.mpr ?_))⟩
  refine ⟨((a,0),v),⟨⟨ha,rfl⟩,mem_sphere_zero_iff_norm.mpr hv⟩,?_⟩
  simpa [Prod.dist_eq, Real.dist_eq,abs_of_pos hr,hr.le] using h

/-- Uniform screened Riesz subtraction on a compact set of centres. The
remainder is an ambient smooth function in centre, separation length and unit
direction. Its mixed derivatives of every order are uniformly bounded there. -/
theorem screened_remainder {σ : ℂ → ℝ} (simple : SimpleDiskTarget.SimpleMetric σ)
    {K : Set ℂ} (compact : IsCompact K) (inside : K ⊆ ball (0:ℂ) 1) :
    ∃ L : ℂ × ℂ → ℂ, ∃ R : RadialParameter → ℝ, ∃ δ > 0,
      ContDiff ℝ ∞ R ∧
      (∀ a ∈ ball (0:ℂ) 1, ∃ C : Coordinates σ a,
        ∀ y ∈ ball (0:ℂ) 1, C.density y = jointDensity L (a,y)) ∧
      (∀ a ∈ K, ∀ v : ℂ, ‖v‖ = 1 → ∀ r : ℝ, 0 < r → r < δ →
        jointDensity L (a,a+r • v) = Real.exp (σ a) * Real.exp (-r) / r + R ((a,r),v)) ∧
      ∀ m : ℕ, ∃ M : ℝ, ∀ a ∈ K, ∀ v : ℂ, ‖v‖ = 1 → ∀ r ∈ Icc 0 δ,
        ‖iteratedFDeriv ℝ m R ((a,r),v)‖ ≤ M := by
  obtain ⟨L,A,sA,geometric,amplitude⟩ := compact_radial_amplitude simple compact.isClosed inside
  let F (p : RadialParameter) := A p - Real.exp (σ p.1.1) * Real.exp (-p.1.2)
  have sF : ContDiff ℝ ∞ F := sA.sub ((Real.contDiff_exp.comp (simple.smooth.comp
    (contDiff_fst.comp contDiff_fst))).mul (Real.contDiff_exp.comp (contDiff_snd.comp contDiff_fst).neg))
  obtain ⟨R,sR,divided⟩ := radial_division sF
  let good := {p : RadialParameter | 0 < p.1.2 → p.1.2 * jointDensity L (p.1.1,p.1.1+p.1.2 • p.2) = A p}
  obtain ⟨δ,hδ,use⟩ := uniform_radius (good := good) compact (fun a ha v hv => (amplitude a ha v hv).2.2)
  refine ⟨L,R,δ,hδ,sR,geometric,?_,?_⟩
  · intro a ha v hv r hr h
    have e := divided a r v
    simp only [F,(amplitude a ha v hv).2.1,neg_zero,Real.exp_zero,mul_one,sub_self,sub_zero] at e
    have eq := use a ha v hv r hr h hr
    change r * jointDensity L (a,a+r • v) = A ((a,r),v) at eq
    field_simp
    linarith
  · intro m
    let T := (K ×ˢ Icc (0:ℝ) δ) ×ˢ sphere (0:ℂ) 1
    have hT : IsCompact T := (compact.prod isCompact_Icc).prod (isCompact_sphere _ _)
    obtain ⟨M,hM⟩ := hT.bddAbove_image (sR.continuous_iteratedFDeriv (m := m) (by exact_mod_cast le_top)).norm.continuousOn
    exact ⟨M,fun a ha v hv r hr => hM ⟨((a,r),v),⟨⟨ha,hr⟩,mem_sphere_zero_iff_norm.mpr hv⟩,rfl⟩⟩

end TransportOkaGrauert.ScalarGeneralKernel
