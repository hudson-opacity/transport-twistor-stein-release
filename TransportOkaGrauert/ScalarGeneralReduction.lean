import TransportOkaGrauert.ScalarGeneralTransport
import TransportOkaGrauert.ScalarGeneral
import TransportOkaGrauert.CoefficientBridge
import TransportOkaGrauert.GeneralSteinReduction

/-! A concrete positive-frequency projection and two invariant moments suffice
for exact scalar pencil transport on a simple disk. The unrestricted primitive
is constructed from the actual flow. All comparisons below use normalized
Haar coefficients and the chart geodesic vector. -/
noncomputable section
namespace TransportOkaGrauert.ScalarGeneralReduction
open Complex Metric Set MeasureTheory ChartCoefficients ScalarGeneralTransport PencilLifts ChartCorrespondence
open scoped ContDiff ComplexConjugate
local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

abbrev trace (p : DiskFunction) : Trace := fun z w => p.val (z,(w:ℂ))

/-- Jointly smooth positive-frequency disk lifting. -/
def HardyProjector : Prop := ∀ u : Trace, ContDiff ℝ ∞ (lifted u) → ∃ p : DiskFunction,
  ∀ z ∈ disk, ∀ k : ℤ, coefficient (trace p) k z = if 0 ≤ k then coefficient u k z else 0

/-- The two adjacent scalar moments in the unattenuated invariant extension
lemma, in modes −2 and −1. -/
def AdjacentMoments (σ : ℂ → ℝ) : Prop := ∀ a b : ℂ → ℂ, ContDiff ℝ ∞ a → ContDiff ℝ ∞ b →
  ∃ h : Trace, ContDiff ℝ ∞ (lifted h) ∧ (∀ z ∈ disk, ∀ w, Isothermal.geodesicX σ h z w = 0) ∧
    ∀ z ∈ disk, coefficient h (-2) z = a z ∧ coefficient h (-1) z = b z

theorem trace_smooth (p : DiskFunction) : ContDiff ℝ ∞ (lifted (trace p)) := by
  apply p.smooth.comp (contDiff_fst.prodMk _)
  simp only [Circle.coe_exp]
  exact ((Complex.ofRealCLM.contDiff.comp contDiff_snd).mul contDiff_const).cexp

theorem smooth_coefficient {u : Trace} (hu : ContDiff ℝ ∞ (lifted u)) (k : ℤ) :
    ContDiff ℝ ∞ (coefficient u k) := by
  let g (p : ℂ × ℝ) := fourier (-k) (p.2 : DiskSeries.Angle) * lifted u p
  have hg : ContDiff ℝ ∞ g := by
    apply ContDiff.mul _ hu
    simp only [fourier_coe_apply, div_eq_mul_inv]
    exact ((contDiff_const.mul (Complex.ofRealCLM.contDiff.comp contDiff_snd)).mul contDiff_const).cexp
  have he : coefficient u k = fun y => (1 / (2*Real.pi) : ℝ) • ∫ t in (0:ℝ)..2*Real.pi, g (y,t) := by
    funext y
    unfold coefficient
    rw [fourierCoeff_eq_intervalIntegral _ _ 0, zero_add]
    simp only [g,lifted,smul_eq_mul,ChartModes.toCircle_angle]
  rw [he]
  exact (ScalarGeneralCauchy.integral_smooth hg Real.two_pi_pos).const_smul _

theorem circle_cont {u : Trace} (hu : ContDiff ℝ ∞ (lifted u)) (z : ℂ) :
    Continuous (fun θ : DiskSeries.Angle => u z θ.toCircle) := by
  apply continuous_coinduced_dom.mpr
  change Continuous (fun t : ℝ => u z (AddCircle.toCircle (t : DiskSeries.Angle)))
  simp only [ChartModes.toCircle_angle]
  exact hu.continuous.comp (continuous_const.prodMk continuous_id)

theorem coeff_sub {u h : Trace} (hu : ContDiff ℝ ∞ (lifted u)) (hh : ContDiff ℝ ∞ (lifted h))
    (k : ℤ) (z : ℂ) : coefficient (fun y w => u y w - h y w) k z = coefficient u k z - coefficient h k z := by
  have hi (v : Trace) (hv : ContDiff ℝ ∞ (lifted v)) :
      Integrable (fun x : DiskSeries.Angle => fourier (-k) x • v z x.toCircle) AddCircle.haarAddCircle :=
    ((fourier (-k)).continuous.smul (circle_cont hv z)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  simp only [coefficient, fourierCoeff, smul_sub, integral_sub (hi u hu) (hi h hh)]

theorem neighbors {u : Trace} (hu : ContDiff ℝ ∞ (lifted u)) (σ : ℂ → ℝ) (z : ℂ) (k : ℤ) :
    coefficient (Isothermal.geodesicX σ u) k z = (Real.exp (-σ z) : ℂ) *
      (neighbor σ u z 1 (k-1) + neighbor σ u z (-1) (k+1)) :=
  coefficient_geodesicX σ u z k (fun _ => hu.contDiffAt.of_le (by decide))
    ((hu.comp (contDiff_const.prodMk contDiff_id)).of_le (by decide))

theorem neighbor_eq {σ : ℂ → ℝ} {u h : Trace} {z : ℂ} (hz : z ∈ disk) (s : ℂ) (k : ℤ)
    (e : EqOn (coefficient u k) (coefficient h k) disk) : neighbor σ u z s k = neighbor σ h z s k := by
  have H := Filter.mem_of_superset (isOpen_ball.mem_nhds hz) (fun x hx => e hx)
  simp only [neighbor, (show coefficient u k =ᶠ[nhds z] coefficient h k from H).fderiv_eq, e hz]

theorem neighbor_zero {σ : ℂ → ℝ} {u : Trace} {z : ℂ} (hz : z ∈ disk) (s : ℂ) (k : ℤ)
    (e : ∀ x ∈ disk, coefficient u k x = 0) : neighbor σ u z s k = 0 := by
  have H : coefficient u k =ᶠ[nhds z] fun _ => 0 := Filter.mem_of_superset (isOpen_ball.mem_nhds hz) (fun x hx => e x hx)
  simp [neighbor,H.fderiv_eq,e z hz]

theorem geodesic_cont {u : Trace} (hu : ContDiff ℝ ∞ (lifted u)) (σ : ℂ → ℝ) (z : ℂ) :
    Continuous (fun θ : DiskSeries.Angle => Isothermal.geodesicX σ u z θ.toCircle) :=
  CoefficientBridge.derivX_entry_continuous (U := fun p v (_ _ : Fin 1) => u p v) (lam := σ) (i := 0) (j := 0)
    (fun _ => hu.contDiffAt.of_le (by decide))

/-- Projecting a primitive with zero modes −2 and −1 retains its entire
geodesic derivative whenever the source has no modes below −1. -/
theorem transport_projection {σ : ℂ → ℝ} {u f : Trace} (hu : ContDiff ℝ ∞ (lifted u))
    (hf : ContDiff ℝ ∞ (lifted f)) (p : DiskFunction)
    (hp : ∀ z ∈ disk, ∀ k : ℤ, coefficient (trace p) k z = if 0 ≤ k then coefficient u k z else 0)
    (gap : ∀ z ∈ disk, coefficient u (-2) z = 0 ∧ coefficient u (-1) z = 0)
    (low : ∀ z ∈ disk, ∀ k : ℤ, k < -1 → coefficient f k z = 0)
    (sol : ∀ z ∈ disk, ∀ w, Isothermal.geodesicX σ u z w = f z w) :
    ∀ z ∈ disk, ∀ w, Isothermal.geodesicX σ (trace p) z w = f z w := by
  intro z hz
  have co (k : ℤ) : coefficient (Isothermal.geodesicX σ (trace p)) k z = coefficient f k z := by
    rw [neighbors (trace_smooth p)]
    by_cases hk : k < -1
    · have neg (s : ℂ) (l : ℤ) (hl : l < 0) : neighbor σ (trace p) z s l = 0 :=
        neighbor_zero hz s l (fun x hx => by simpa [not_le.mpr hl] using hp x hx l)
      rw [neg _ _ (by omega), neg _ _ (by omega), low z hz k hk,zero_add,mul_zero]
    · have same (l : ℤ) (hl : -2 ≤ l) (s : ℂ) : neighbor σ (trace p) z s l = neighbor σ u z s l := by
        apply neighbor_eq hz
        intro x hx
        rw [hp x hx]
        split_ifs with h
        · rfl
        · rcases (show l = -2 ∨ l = -1 by omega) with rfl | rfl
          · exact (gap x hx).1.symm
          · exact (gap x hx).2.symm
      rw [same _ (by omega), same _ (by omega), ← neighbors hu]
      unfold coefficient
      simp only [sol z hz]
  have eq := CoefficientBridge.eq_of_coeff_eq (geodesic_cont (trace_smooth p) σ z) (circle_cont hf z) co
  intro w
  let θ : DiskSeries.Angle := ((w:ℂ).arg : ℝ)
  have he : θ.toCircle = w := (ChartModes.toCircle_angle _).trans (Circle.exp_arg w)
  simpa only [he] using congrFun eq θ


theorem X_sub {σ : ℂ → ℝ} {u h : Trace} (hu : ContDiff ℝ ∞ (lifted u))
    (hh : ContDiff ℝ ∞ (lifted h)) (z : ℂ) (w : Circle) :
    Isothermal.geodesicX σ (fun p v => u p v - h p v) z w =
      Isothermal.geodesicX σ u z w - Isothermal.geodesicX σ h z w := by
  let θ := (w:ℂ).arg
  let p := (z,θ)
  have eq : Circle.exp θ = w := Circle.exp_arg w
  have d := hu.differentiable (by simp) p
  have e := hh.differentiable (by simp) p
  rw [← eq,PathContinuation.geodesicX_eq_chart_derivative _ _ _ θ (d.sub e),
    PathContinuation.geodesicX_eq_chart_derivative _ _ _ θ d,PathContinuation.geodesicX_eq_chart_derivative _ _ _ θ e]
  exact congrArg (fun L : GeodesicFlowExtension.State →L[ℝ] ℂ => L (PathContinuation.chartVector σ p))
    ((d.hasFDerivAt.sub e.hasFDerivAt).fderiv)

/-- Exact scalar pencil solvability from an invariant extension of just two
adjacent moments and the smooth disk lifting of the positive Fourier part. -/
theorem solvable {σ : ℂ → ℝ} (simple : SimpleDiskTarget.SimpleMetric σ)
    (project : HardyProjector) (extend : AdjacentMoments σ) : ScalarSolvability σ := by
  apply (ScalarGeneral.scalarSolvability_iff σ).mpr
  intro g
  let f : Trace := fun z w => (Real.exp (-σ z) : ℂ) * g.val (z,w)
  have hf : ContDiff ℝ ∞ (lifted f) := (Complex.ofRealCLM.contDiff.comp
    (simple.smooth.comp contDiff_fst).neg.exp).mul (trace_smooth g)
  obtain ⟨u,hu,du⟩ := smooth_primitive simple f hf
  obtain ⟨h,hh,dh,mom⟩ := extend (coefficient u (-2)) (coefficient u (-1)) (smooth_coefficient hu _) (smooth_coefficient hu _)
  let v : Trace := fun z w => u z w - h z w
  have hv : ContDiff ℝ ∞ (lifted v) := hu.sub hh
  obtain ⟨p,proj⟩ := project v hv
  have gap (z : ℂ) (hz : z ∈ disk) : coefficient v (-2) z = 0 ∧ coefficient v (-1) z = 0 := by
    simp [v,coeff_sub hu hh,(mom z hz).1,(mom z hz).2]
  have low (z : ℂ) (hz : z ∈ disk) (k : ℤ) (hk : k < -1) : coefficient f k z = 0 := by
    have H : DiffContOnCl ℂ (fun w => g.val (z,w)) disk :=
      ⟨g.fibre z hz,(g.smooth.continuous.comp (continuous_const.prodMk continuous_id)).continuousOn⟩
    change fourierCoeff (fun θ : DiskSeries.Angle => (Real.exp (-σ z) : ℂ) * g.val (z,(θ.toCircle:ℂ))) k = 0
    rw [fourierCoeff.const_mul]
    change _ * fourierCoeff (BoundaryModes.boundaryTrace (fun w => g.val (z,w))) k = 0
    rw [BoundaryModes.negativeMode_eq_zero H k (by omega),mul_zero]
  have ds (z : ℂ) (hz : z ∈ disk) (w : Circle) : Isothermal.geodesicX σ v z w = f z w := by
    change Isothermal.geodesicX σ (fun y w => u y w - h y w) z w = _
    rw [X_sub hu hh,du z (ball_subset_closedBall hz),dh z hz,sub_zero]
  have solved := transport_projection hv hf p proj gap low ds
  refine ⟨p,?_⟩
  intro z hz w
  have H := solved z hz w
  change Isothermal.geodesicX σ (fun a v => p.val (a,(v:ℂ))) z w = (Real.exp (-σ z) : ℂ) * g.val (z,w) at H
  rw [geodesicX_trace p.smooth] at H
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)) H

/-- Fixed-chart Steinness from the adjacent scalar invariant moments, smooth
positive projection and the radial geometry of the pencil. -/
theorem stein {σ : ℂ → ℝ} (simple : SimpleDiskTarget.SimpleMetric σ) (project : HardyProjector)
    (extend : AdjacentMoments σ) (radial : ∀ a : ChartStein.ClosedDisk, Nonempty (PencilGeometry.Data σ a))
    (U : Set ℂ) (openU : IsOpen U) (subU : U ⊆ disk) : ChartStein.HasSteinProperties σ U :=
  GeneralSteinReduction.for_metric simple (solvable simple project extend) radial U openU subU

end TransportOkaGrauert.ScalarGeneralReduction
