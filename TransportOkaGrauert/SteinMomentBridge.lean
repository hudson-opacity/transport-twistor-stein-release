import TransportOkaGrauert.HardyDisk
import TransportOkaGrauert.SimpleRadialGeometry
import TransportOkaGrauert.ScalarGeneralMeanSolver
import TransportOkaGrauert.ManifoldStein

/-! # The remaining scalar X-ray input in geometric form
The original base disk is strictly inside a larger simple disk. Consequently
an invariant trace on the larger disk only needs to be smooth at its interior
points; cutting it off supplies a globally smooth representative. -/
namespace TransportOkaGrauert.SteinMomentBridge
noncomputable section
open Set Metric Filter Complex SimpleDiskTarget PencilLifts ScalarGeneralTransport
open ChartCoefficients SimpleEnlargement
open scoped ContDiff Topology

/-- The interior smooth-invariant moment statement on a simple chart.
The Haar coefficient uses the probability measure on the angular circle. -/
def InteriorMeanStatement : Prop := ∀ σ : ℂ → ℝ, SimpleMetric σ → ∀ a : ℂ → ℂ, ContDiff ℝ ∞ a →
  ∃ h : Trace, (∀ z ∈ disk, ∀ t, ContDiffAt ℝ ∞ (lifted h) (z,t)) ∧
    (∀ z ∈ disk, ∀ w, Isothermal.geodesicX σ h z w = 0) ∧
    ∀ z ∈ disk, coefficient h 0 z = a z

/-- Solving the mean equation on every smaller concentric disk is sufficient.
The angular solution remains smooth and invariant on the larger open disk. -/
def CompactInteriorMeanStatement : Prop := ∀ σ : ℂ → ℝ, SimpleMetric σ → ∀ a : ℂ → ℂ,
  ContDiff ℝ ∞ a → ∀ r : ℝ, 0 < r → r < 1 → ∃ h : Trace,
    (∀ z ∈ disk, ∀ t, ContDiffAt ℝ ∞ (lifted h) (z,t)) ∧
    (∀ z ∈ disk, ∀ w, Isothermal.geodesicX σ h z w = 0) ∧
    ∀ z ∈ ball (0:ℂ) r, coefficient h 0 z = a z

/-- Localization of the transport equation as well as the data. A
globally smooth trace need only be invariant on the smaller disk. -/
def LocalMeanStatement : Prop := ∀ σ : ℂ → ℝ, SimpleMetric σ → ∀ a : ℂ → ℂ,
  ContDiff ℝ ∞ a → ∀ r : ℝ, 0 < r → r < 1 → ∃ h : Trace,
    (∀ z ∈ disk, ∀ t, ContDiffAt ℝ ∞ (lifted h) (z,t)) ∧
    (∀ z ∈ ball (0:ℂ) r, ∀ w, Isothermal.geodesicX σ h z w = 0) ∧
    ∀ z ∈ ball (0:ℂ) r, coefficient h 0 z = a z

/-- The published smooth-invariant statement can be used without assuming
any ambient extension or two-sided regularity of the invariant at the boundary. -/
theorem mean_from_local (moment : LocalMeanStatement) {σ : ℂ → ℝ} (hs : SimpleMetric σ) :
    ScalarGeneralMean.MeanSurjectivity σ := by
  intro a ha
  obtain ⟨R,hR,τ,simple,smooth,e,he,agrees⟩ := exists_simple_enlargement hs
  have hr : 0 < R := zero_lt_one.trans hR
  let m : ℂ →L[ℝ] ℂ := R⁻¹ • ContinuousLinearMap.id ℝ ℂ
  have im (z : ℂ) : R • m z = z := by simp [m,hr.ne']
  have msmall {z : ℂ} (hz : ‖z‖ < R) : m z ∈ disk := by
    rw [mem_ball_zero_iff]
    change ‖R⁻¹ • z‖ < 1
    rw [norm_smul,Real.norm_of_nonneg (inv_pos.mpr hr).le,←div_eq_inv_mul]
    exact (div_lt_one hr).mpr hz
  have inner_disk {z : ℂ} (hz : z ∈ disk) : m z ∈ ball (0:ℂ) R⁻¹ := by
    rw [mem_ball_zero_iff]
    change ‖R⁻¹ • z‖ < R⁻¹
    rw [norm_smul,Real.norm_of_nonneg (inv_pos.mpr hr).le]
    simpa using mul_lt_mul_of_pos_left (mem_ball_zero_iff.mp hz) (inv_pos.mpr hr)
  let b (z : ℂ) := a (R • z)
  obtain ⟨h,sh,inv,avg⟩ := moment _ simple b (ha.comp (contDiff_id.const_smul R)) R⁻¹ (inv_pos.mpr hr) (inv_lt_one_of_one_lt₀ hR)
  let β : ContDiffBump (0 : ℂ) := ⟨1,(1+R)/2,one_pos,by linarith⟩
  let v : Trace := fun z w => β z • h (m z) w
  have shrink (p : ℂ × ℝ) (hz : ‖p.1‖ < R) :
      ContDiffAt ℝ ∞ (fun q : ℂ × ℝ => h (m q.1) (Circle.exp q.2)) p :=
    (sh _ (msmall hz) p.2).comp p ((m.contDiff.comp contDiff_fst).prodMk contDiff_snd).contDiffAt
  have sv : ContDiff ℝ ∞ (lifted v) := by
    apply contDiff_iff_contDiffAt.mpr
    intro p
    by_cases hsmall : ‖p.1‖ < R
    · exact ((β.contDiff.comp contDiff_fst).contDiffAt.smul (shrink p hsmall))
    · have outside : β.rOut < ‖p.1‖ := by change (1+R)/2 < _; linarith [le_of_not_gt hsmall]
      apply (contDiffAt_const (c := (0:ℂ))).congr_of_eventuallyEq
      filter_upwards [continuous_fst.norm.continuousAt.eventually_const_lt outside] with q hq
      simp [lifted,v,β.zero_of_le_dist (x := q.1) (by simpa using hq.le)]
  refine ⟨v,sv,?_,?_⟩
  · intro z hz w
    have hz1 := mem_ball_zero_iff.mp hz
    have mz := msmall (hz1.trans hR)
    have hβ := β.eventuallyEq_one_of_mem_ball (x := z) hz
    have hbase : (fun q => v q w) =ᶠ[𝓝 z] (fun q => h (m q) w) :=
      hβ.mono fun q hq => by simp [v,hq]
    have angle : DifferentiableAt ℝ (fun q => h q w) (m z) := by
      have hh := (sh _ mz (w:ℂ).arg).differentiableAt (by simp)
      have line : DifferentiableAt ℝ (fun x : ℂ => (x,(w:ℂ).arg)) (m z) :=
        differentiableAt_id.prodMk (differentiableAt_const _)
      simpa only [lifted,Function.comp_def,Circle.exp_arg] using hh.comp (m z) line
    have flat : Fourier.flatX v z w = (R⁻¹:ℝ) • Fourier.flatX h (m z) w := by
      unfold Fourier.flatX
      rw [hbase.fderiv_eq]
      have d := angle.hasFDerivAt.comp z m.hasFDerivAt
      change fderiv ℝ ((fun q => h q w) ∘ m) z w = _
      rw [d.fderiv]
      exact (fderiv ℝ (fun q => h q w) (m z)).map_smul R⁻¹ (w:ℂ)
    have vertical : Isothermal.vertical v z w = Isothermal.vertical h (m z) w := by
      simp [Isothermal.vertical,v,hβ.eq_of_nhds]
    have same : τ =ᶠ[𝓝 z] σ := by
      have hq : Complex.normSq z < 1+e := by rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg z]
      exact (Complex.continuous_normSq.continuousAt.eventually_lt_const hq).mono fun y hy => agrees y hy
    have drift : Isothermal.angularDrift (rescale τ R) (m z) w = R * Isothermal.angularDrift σ z w := by
      simp only [Isothermal.angularDrift,rescale_fderiv smooth,im,same.fderiv_eq]
      ring
    have ih := inv _ (inner_disk hz) w
    rw [Isothermal.geodesicX,drift] at ih
    have equation := (mul_eq_zero.mp ih).resolve_left (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _))
    rw [Isothermal.geodesicX,flat,vertical,Complex.real_smul,Complex.ofReal_inv]
    suffices (R:ℂ)⁻¹ * Fourier.flatX h (m z) w + Isothermal.angularDrift σ z w * Isothermal.vertical h (m z) w = 0 by simp [this]
    have hn : (R:ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    rw [Complex.ofReal_mul] at equation
    field_simp [hn]
    linear_combination equation
  · intro z hz
    have hb := β.one_of_mem_closedBall (x := z) (ball_subset_closedBall hz)
    have H := avg (m z) (inner_disk hz)
    simp only [v,coefficient,hb,one_smul,b,im] at H ⊢
    exact H

theorem mean_from_compact (moment : CompactInteriorMeanStatement) {σ : ℂ → ℝ} (hs : SimpleMetric σ) :
    ScalarGeneralMean.MeanSurjectivity σ := by
  apply mean_from_local _ hs
  intro τ simple a ha r hp hr
  obtain ⟨h,sh,inv,avg⟩ := moment τ simple a ha r hp hr
  exact ⟨h,sh,fun z hz => inv z (ball_subset_ball hr.le hz),avg⟩

theorem mean_from_interior (moment : InteriorMeanStatement) {σ : ℂ → ℝ} (hs : SimpleMetric σ) :
    ScalarGeneralMean.MeanSurjectivity σ := by
  apply mean_from_compact _ hs
  intro τ simple a ha r _ hr
  obtain ⟨h,sh,inv,avg⟩ := moment τ simple a ha
  exact ⟨h,sh,inv,fun z hz => avg z (ball_subset_ball hr.le hz)⟩

/-- Without using the scalar one-moment simplification, the geometric and
Hardy inputs are already closed for every simple disk. -/
theorem chart_of_adjacent {σ : ℂ → ℝ} (hs : SimpleMetric σ) (hm : ScalarGeneralReduction.AdjacentMoments σ) :
    ∀ U, IsOpen U → U ⊆ disk → ChartStein.HasSteinProperties σ U :=
  ScalarGeneralReduction.stein hs HardyDisk.projector hm (SimpleRadialGeometry.global_radial_data hs)

/-- The chart version requires only the scalar invariant mean theorem. -/
theorem chart_of_mean {σ : ℂ → ℝ} (simple : SimpleMetric σ)
    (mean : ScalarGeneralMean.MeanSurjectivity σ) :
    ∀ U, IsOpen U → U ⊆ disk → ChartStein.HasSteinProperties σ U :=
  GeneralSteinReduction.for_metric simple (ScalarGeneralMeanSolver.solvable simple HardyDisk.projector mean)
    (SimpleRadialGeometry.global_radial_data simple)

/-- Both exact universal conclusions follow from the interior form of the
scalar adjoint X-ray range theorem. -/
theorem universal_of_interior_mean (h : InteriorMeanStatement) :
    ChartStein.GeneralSimpleSurfaceStatement ∧ ManifoldStein.GeneralManifoldStatement := by
  have chart : ChartStein.GeneralSimpleSurfaceStatement := fun _ hs => chart_of_mean hs (mean_from_interior h hs)
  exact ⟨chart,ManifoldStein.manifold_of_chart chart⟩

end
end TransportOkaGrauert.SteinMomentBridge
