import TransportOkaGrauert.SimpleEnlargement
import TransportOkaGrauert.SimpleRadialFrame

/-! # Global radial pencils, including boundary centres

Apply radial normal coordinates on a simple enlargement. Dilation of
coordinates pulls all four smooth fields back to the original disk.
The radial Hessian and connection equations transform by the same
factor as the derivative of the dilation.
-/

noncomputable section
namespace TransportOkaGrauert.SimpleRadialGeometry

open Complex ChartStein ChartCorrespondence PencilGeometry SteinDivisor
open SimpleDiskTarget SimpleEnlargement SimpleRadialFrame Set Metric Filter
open scoped ContDiff ComplexConjugate Topology

private def shrink (R : ℝ) : ℂ →L[ℝ] ℂ := R⁻¹ • ContinuousLinearMap.id ℝ ℂ

private theorem angular (σ : ℂ → ℝ) (z : ℂ) (w : Circle) :
    fderiv ℝ σ z (I * (w : ℂ)) = Isothermal.angularDrift σ z w := by
  have e : I*(w:ℂ) = -(w:ℂ).im • (1 : ℂ) + (w:ℂ).re • I := by
    apply Complex.ext <;> simp [Complex.real_smul]
  rw [e,map_add,map_smul,map_smul]
  simp only [smul_eq_mul,Isothermal.angularDrift]
  ring

theorem global_radial_data {σ : ℂ → ℝ} (simple : SimpleMetric σ) (a : ClosedDisk) :
    Nonempty (PencilGeometry.Data σ a) := by
  obtain ⟨R,hR,τ,sl,sτ,e,he,eq⟩ := exists_simple_enlargement simple
  have hr := zero_lt_one.trans hR
  let m := shrink R
  have hm (z : ℂ) : R • m z = z := by simp [m,shrink,hr.ne']
  have hm_norm (z : ℂ) : ‖m z‖ = R⁻¹ * ‖z‖ := by simp [m,shrink,Real.norm_of_nonneg hr.le]
  let S := m '' closedBall (0:ℂ) 1
  have comp : IsCompact S := (isCompact_closedBall (0:ℂ) 1).image m.continuous
  have small : S ⊆ ball (0:ℂ) 1 := by
    rintro _ ⟨z,hz,rfl⟩
    rw [mem_ball_zero_iff,hm_norm,←div_eq_inv_mul]
    exact (div_lt_one hr).mpr ((mem_closedBall_zero_iff.mp hz).trans_lt hR)
  have mem (z : ClosedDisk) : m z.val ∈ S := ⟨z.val,z.property,rfl⟩
  obtain ⟨d⟩ := fields_on_compact sl (mem_ball_zero_iff.mp (small (mem a))) comp small
  have same (z : ClosedDisk) : τ =ᶠ[𝓝 z.val] σ := by
    have hz : ‖z.val‖ ≤ 1 := mem_closedBall_zero_iff.mp z.property
    have hn : Complex.normSq z.val < 1+e := by rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg z.val]
    exact (Complex.continuous_normSq.continuousAt.eventually_lt_const hn).mono fun y hy => eq y hy
  have scale (z : ClosedDisk) : Real.exp (rescale τ R (m z)) = R * Real.exp (σ z) := by
    rw [rescale,hm,(same z).eq_of_nhds, Real.exp_add,Real.exp_log hr,mul_comm]
  have conn (z : ClosedDisk) (w : ℂ) :
      connection (rescale τ R) d.k d.W d.ρ (m z) w =
        R * connection σ (d.k ∘ m) (d.W ∘ m) (d.ρ ∘ m) z w := by
    simp only [connection,scale,Function.comp_apply]
    ring
  have pull (f : ℂ → ℂ) (sf : ContDiff ℝ ∞ f) (z w : ℂ) :
      fderiv ℝ (f ∘ m) z w = (R⁻¹ : ℝ) • (fderiv ℝ f (m z) w) := by
    rw [fderiv_comp z (sf.differentiable (by simp) _) m.differentiableAt,m.fderiv]
    change fderiv ℝ f (m z) (R⁻¹ • w) = _
    rw [map_smul]
  refine ⟨d.W ∘ m,d.ρ ∘ m,d.c ∘ m,d.k ∘ m,d.smoothW.comp m.contDiff,d.smoothρ.comp m.contDiff,
    d.smoothC.comp m.contDiff,d.smoothK.comp m.contDiff,fun z => d.unitρ _ (mem z),?_,?_,?_⟩
  · intro z
    rw [Function.comp_apply,d.zeroW _ (mem z)]
    exact ⟨fun h => Subtype.ext ((hm z.val) ▸ (hm a.val) ▸ congrArg (fun x : ℂ => R • x) h),
      fun h => h ▸ rfl⟩
  · intro z w
    rw [pull _ d.smoothW, d.hessian _ (mem z),scale,conn]
    simp only [Function.comp_apply,Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_mul]
    field_simp [show (R : ℂ) ≠ 0 by exact_mod_cast hr.ne']
  · intro z hz w
    let q : ClosedDisk := ⟨z,ball_subset_closedBall hz⟩
    rw [pull _ d.smoothρ,d.radialFrame _ (mem q), rescale_fderiv sτ, hm, (same q).fderiv_eq, angular σ z w]
    rw [conn q]
    simp only [Function.comp_apply,Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_mul]
    field_simp [show (R : ℂ) ≠ 0 by exact_mod_cast hr.ne']
    ring

end TransportOkaGrauert.SimpleRadialGeometry
