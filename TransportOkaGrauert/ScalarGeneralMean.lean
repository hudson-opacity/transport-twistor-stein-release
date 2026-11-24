import TransportOkaGrauert.ScalarGeneralReduction
import TransportOkaGrauert.ShiftedModes

/-! The scalar invariant zeroth moment suffices to solve smooth holomorphic
sources modulo a base function. Reversal of velocity then solves odd sources
exactly and fixes the value of their primitive at zero velocity. -/
noncomputable section
namespace TransportOkaGrauert.ScalarGeneralMean
open Complex Metric MeasureTheory Set ChartCoefficients ScalarGeneralTransport ScalarGeneralReduction PencilLifts ChartCorrespondence
open scoped ContDiff ComplexConjugate
local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

/-- The scalar adjoint X-ray transform, written as prescription of the zeroth
Haar coefficient of a smooth invariant trace. -/
def MeanSurjectivity (σ : ℂ → ℝ) : Prop := ∀ a : ℂ → ℂ, ContDiff ℝ ∞ a →
  ∃ h : Trace, ContDiff ℝ ∞ (lifted h) ∧ (∀ z ∈ disk, ∀ w, Isothermal.geodesicX σ h z w = 0) ∧
    ∀ z ∈ disk, coefficient h 0 z = a z

def base (f : ℂ → ℂ) (hf : ContDiff ℝ ∞ f) : DiskFunction where
  val p := f p.1
  smooth := hf.comp contDiff_fst
  fibre z _ := differentiableOn_const (f z)

private theorem const_mode (c : ℂ) (k : ℤ) :
    fourierCoeff (fun _ : DiskSeries.Angle => c) k = if k = 0 then c else 0 := by
  have he : (fun _ : DiskSeries.Angle => c) = fun t => c * fourier 0 t := by simp
  rw [he,fourierCoeff.const_mul,fourierCoeff_fourier]
  by_cases h : k = 0
  · subst k; simp
  · simp [h]

private theorem negative_trace (f : DiskFunction) (z : ℂ) (hz : z ∈ disk) (k : ℤ) (hk : k < 0) :
    coefficient (trace f) k z = 0 :=
  BoundaryModes.negativeMode_eq_zero (f := fun w => f.val (z,w)) ⟨f.fibre z hz,
    (f.smooth.continuous.comp (continuous_const.prodMk continuous_id)).continuousOn⟩ _ hk

/-- The zeroth Haar coefficient of an actual disk trace is the centre value. -/
theorem center_mode (f : DiskFunction) (z : ℂ) (hz : z ∈ disk) : coefficient (trace f) 0 z = f.val (z,0) := by
  obtain ⟨g,H⟩ := ScalarGeneral.divide_at_zero f
  have he : (fun θ : DiskSeries.Angle => trace f z θ.toCircle) =
      (fun θ => (θ.toCircle:ℂ) * trace g z θ.toCircle) + (fun _ => f.val (z,0)) := by
    funext θ
    exact (sub_eq_iff_eq_add'.mp (H z hz _ (sphere_subset_closedBall θ.toCircle.property)).symm).trans (add_comm ..)
  have hc : Continuous (fun θ : DiskSeries.Angle => (θ.toCircle:ℂ) * trace g z θ.toCircle) := (continuous_subtype_val.comp AddCircle.continuous_toCircle).mul (circle_cont (trace_smooth g) z)
  unfold coefficient
  rw [he,fourierCoeff.add (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    ((continuous_const (y := f.val (z,0))).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  change fourierCoeff (fun θ : DiskSeries.Angle => (θ.toCircle:ℂ) * trace g z θ.toCircle) 0 +
    fourierCoeff (fun _ : DiskSeries.Angle => f.val (z,0)) 0 = _
  rw [ShiftedModes.coeff_shift, const_mode, if_pos rfl]
  change coefficient (trace g) (-1) z + f.val (z,0) = _
  rw [negative_trace g z hz (-1) (by decide),zero_add]

private theorem x_smooth {σ : ℂ → ℝ} (hs : ContDiff ℝ ∞ σ) {u : Trace} (hu : ContDiff ℝ ∞ (lifted u)) :
    ContDiff ℝ ∞ (lifted (Isothermal.geodesicX σ u)) := by
  have hX : ContDiff ℝ ∞ (PathContinuation.chartVector σ) := contDiff_iff_contDiffAt.mpr
    (fun p => ChartRegularity.chartVector_contDiffAt p hs.contDiffAt)
  have eq : lifted (Isothermal.geodesicX σ u) = fun p => fderiv ℝ (lifted u) p (PathContinuation.chartVector σ p) :=
    funext fun p => PathContinuation.geodesicX_eq_chart_derivative _ _ _ _ (hu.differentiable (by simp) p)
  rw [eq]
  exact (hu.fderiv_right (m := ∞) (by simp)).clm_apply hX

/-- With a zero centre normalization, the whole transport error has only the
zeroth coefficient, hence is a smooth function of the base alone. -/
theorem solve_modulo_base {σ : ℂ → ℝ} (simple : SimpleDiskTarget.SimpleMetric σ) (project : HardyProjector)
    (mean : MeanSurjectivity σ) (g : DiskFunction) : ∃ P : DiskFunction, ∃ a : ℂ → ℂ, ContDiff ℝ ∞ a ∧
      (∀ z ∈ disk, P.val (z,0) = 0) ∧ ∀ z ∈ disk, ∀ w : Circle,
        boundaryTransport σ P.val z w = g.val (z,w) + a z := by
  let scale (z : ℂ) := (Real.exp (-σ z) : ℂ)
  have hscale : ContDiff ℝ ∞ scale := Complex.ofRealCLM.contDiff.comp simple.smooth.neg.exp
  let f := (base scale hscale).mul g
  have hf := trace_smooth f
  obtain ⟨u,hu,du⟩ := smooth_primitive simple (trace f) hf
  obtain ⟨h,hh,dh,m⟩ := mean (coefficient u 0) (smooth_coefficient hu 0)
  let v : Trace := fun z w => u z w - h z w
  have hv : ContDiff ℝ ∞ (lifted v) := hu.sub hh
  obtain ⟨p,hp⟩ := project v hv
  have pzero (z : ℂ) (hz : z ∈ disk) : coefficient (trace p) 0 z = 0 := by
    rw [hp z hz, if_pos le_rfl]; simp [v,coeff_sub hu hh,m z hz]
  have sol (z : ℂ) (hz : z ∈ disk) : Isothermal.geodesicX σ v z = trace f z := by
    funext w
    change Isothermal.geodesicX σ (fun y a => u y a - h y a) z w = _
    rw [X_sub hu hh,du z (ball_subset_closedBall hz),dh z hz,sub_zero]
  let d : Trace := fun z w => Isothermal.geodesicX σ (trace p) z w - trace f z w
  have hx := x_smooth simple.smooth (trace_smooth p)
  have hd : ContDiff ℝ ∞ (lifted d) := hx.sub hf
  let c := coefficient d 0
  have modes (z : ℂ) (hz : z ∈ disk) (k : ℤ) (hk : k ≠ 0) : coefficient d k z = 0 := by
    change coefficient (fun y w => Isothermal.geodesicX σ (trace p) y w - trace f y w) k z = 0
    rw [coeff_sub hx hf,sub_eq_zero,neighbors (trace_smooth p)]
    by_cases hneg : k < 0
    · have vanish (s : ℂ) (l : ℤ) (hl : l ≤ 0) : neighbor σ (trace p) z s l = 0 := by
        apply neighbor_zero hz
        intro y hy
        rcases hl.eq_or_lt with rfl | hn
        · exact pzero y hy
        · simp [hp y hy, not_le.mpr hn]
      rw [vanish _ _ (by omega), vanish _ _ (by omega), zero_add, mul_zero, negative_trace f z hz k hneg]
    · have same (s : ℂ) (l : ℤ) (hl : 0 ≤ l) : neighbor σ (trace p) z s l = neighbor σ v z s l :=
        neighbor_eq hz s l (fun y hy => by simp [hp y hy,hl])
      rw [same _ _ (by omega), same _ _ (by omega), ← neighbors hv]
      simp only [coefficient,sol z hz]
  have constant (z : ℂ) (hz : z ∈ disk) (w : Circle) : d z w = c z := by
    have eq := CoefficientBridge.eq_of_coeff_eq (circle_cont hd z) (g := fun _ => c z) continuous_const (fun k => by
      rw [const_mode]
      by_cases h : k = 0
      · subst k; rfl
      · simpa [h] using modes z hz k h)
    let θ : DiskSeries.Angle := ((w:ℂ).arg : ℝ)
    have he := (ChartModes.toCircle_angle (w:ℂ).arg).trans (Circle.exp_arg w)
    simpa only [θ,he] using congrFun eq θ
  refine ⟨p,fun z => (Real.exp (σ z) : ℂ) * c z,
    (Complex.ofRealCLM.contDiff.comp simple.smooth.exp).mul (smooth_coefficient hd 0),
    fun z hz => (center_mode p z hz).symm.trans (pzero z hz), ?_⟩
  intro z hz w
  have e := constant z hz w
  change Isothermal.geodesicX σ (fun y a => p.val (y,(a:ℂ))) z w - scale z * g.val (z,w) = c z at e
  rw [geodesicX_trace p.smooth] at e
  have hprod : (Real.exp (σ z):ℂ) * scale z = 1 := by
    unfold scale; rw [← Complex.ofReal_mul,← Real.exp_add,add_neg_cancel, Real.exp_zero,Complex.ofReal_one]
  change scale z * boundaryTransport σ p.val z w - scale z * g.val (z,w) = c z at e
  linear_combination (norm := ring) (Real.exp (σ z) : ℂ) * e - (boundaryTransport σ p.val z w - g.val (z,w)) * hprod


def reverse (w : Circle) : Circle := ⟨-(w:ℂ), mem_sphere_zero_iff_norm.mpr (by simp)⟩

@[simp] theorem reverse_coe (w : Circle) : (reverse w : ℂ) = -(w:ℂ) := rfl

/-- Reversal in the velocity coordinate. -/
def reflect (p : DiskFunction) : DiskFunction where
  val q := p.val (q.1,-q.2)
  smooth := p.smooth.comp (contDiff_fst.prodMk contDiff_snd.neg)
  fibre z hz := (p.fibre z hz).comp differentiableOn_id.neg (fun w hw => by simpa [disk] using hw)

private theorem X_reflect (σ : ℂ → ℝ) (p : DiskFunction) (z : ℂ) (w : Circle) :
    boundaryTransport σ (reflect p).val z w = -boundaryTransport σ p.val z (reverse w) := by
  let D := fderiv ℝ p.val (z,-(w:ℂ))
  let v := (z,(w:ℂ))
  have deriv := (p.smooth.differentiable (by simp) (z,-(w:ℂ))).hasFDerivAt.comp v
    ((hasFDerivAt_fst (𝕜 := ℝ) (p := v)).prodMk (hasFDerivAt_snd (𝕜 := ℝ) (p := v)).neg)
  have rev : Isothermal.angularDrift σ z (reverse w) = -Isothermal.angularDrift σ z w := by
    simp [Isothermal.angularDrift]; ring
  have eq : ((w:ℂ),-((Isothermal.angularDrift σ z w : ℂ)*(I*(w:ℂ)))) =
      -((reverse w:ℂ), (Isothermal.angularDrift σ z (reverse w):ℂ)*(I*(reverse w:ℂ))) := by
    ext <;> simp [rev]
  have h := congrArg (fun L : ChartStein.E →L[ℝ] ℂ => L ((w:ℂ),(Isothermal.angularDrift σ z w : ℂ)*(I*w))) deriv.fderiv
  change boundaryTransport σ (reflect p).val z w = D ((w:ℂ),-((Isothermal.angularDrift σ z w : ℂ)*(I*(w:ℂ)))) at h
  rw [h,eq,map_neg]; rfl

/-- Even velocity part of a disk function. -/
def evenPart (p : DiskFunction) : DiskFunction where
  val q := (2:ℂ)⁻¹ * (p.val q + (reflect p).val q)
  smooth := contDiff_const.mul (p.smooth.add (reflect p).smooth)
  fibre z hz := (differentiableOn_const _).mul ((p.fibre z hz).add ((reflect p).fibre z hz))

private theorem X_even (σ : ℂ → ℝ) (p : DiskFunction) (z : ℂ) (w : Circle) :
    boundaryTransport σ (evenPart p).val z w = (boundaryTransport σ p.val z w - boundaryTransport σ p.val z (reverse w))/2 := by
  have d := (((p.smooth.differentiable (by simp) (z,(w:ℂ))).hasFDerivAt.add
    ((reflect p).smooth.differentiable (by simp) (z,(w:ℂ))).hasFDerivAt).const_mul (2:ℂ)⁻¹).fderiv
  have h := congrArg (fun L : ChartStein.E →L[ℝ] ℂ => L ((w:ℂ),(Isothermal.angularDrift σ z w : ℂ)*(I*w))) d
  change boundaryTransport σ (evenPart p).val z w = (2:ℂ)⁻¹ *
    (boundaryTransport σ p.val z w + boundaryTransport σ (reflect p).val z w) at h
  rw [h,X_reflect]; ring

/-- Every odd fibre-holomorphic source has an even disk primitive vanishing
at zero velocity. -/
theorem solve_odd {σ : ℂ → ℝ} (simple : SimpleDiskTarget.SimpleMetric σ) (project : HardyProjector)
    (mean : MeanSurjectivity σ) (g : DiskFunction)
    (odd : ∀ z ∈ disk, ∀ w : Circle, g.val (z,(reverse w:ℂ)) = -g.val (z,w)) :
    ∃ p : DiskFunction, (∀ z ∈ disk, p.val (z,0) = 0) ∧ (∀ z w : ℂ, p.val (z,-w) = p.val (z,w)) ∧
      ∀ z ∈ disk, ∀ w : Circle, boundaryTransport σ p.val z w = g.val (z,w) := by
  obtain ⟨P,a,_,zero,sol⟩ := solve_modulo_base simple project mean g
  refine ⟨evenPart P, fun z hz => by simp [evenPart,reflect,zero z hz], fun z w => by simp [evenPart,reflect,add_comm],?_⟩
  intro z hz w
  rw [X_even,sol z hz,sol z hz,odd z hz]
  ring

end TransportOkaGrauert.ScalarGeneralMean
