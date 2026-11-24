import TransportOkaGrauert.ScalarGeneralMean
import TransportOkaGrauert.ScalarGeneralJets

/-! The smooth scalar adjoint X-ray range theorem for functions suffices for
full holomorphic scalar transport. An invariant rescaling of velocity raises
the parity of a base source; its inverse after division at zero recovers the
required smooth primitive. -/
noncomputable section
namespace TransportOkaGrauert.ScalarGeneralMeanSolver
open Complex Set Metric ScalarGeneralMean ScalarGeneralReduction ScalarGeneralTransport PencilLifts ChartCorrespondence
open scoped ContDiff Topology

private theorem X_mul (σ : ℂ → ℝ) (f g : DiskFunction) (z : ℂ) (w : Circle) :
    boundaryTransport σ (f.mul g).val z w = f.val (z,w) * boundaryTransport σ g.val z w +
      g.val (z,w) * boundaryTransport σ f.val z w := by
  exact congrArg (fun L : ChartStein.E →L[ℝ] ℂ => L ((w:ℂ), (Isothermal.angularDrift σ z w:ℂ)*(I*w)))
    (((f.smooth.differentiable (by simp) (z,(w:ℂ))).hasFDerivAt.mul
    (g.smooth.differentiable (by simp) (z,(w:ℂ))).hasFDerivAt).fderiv)

private theorem X_exp (σ : ℂ → ℝ) (f : DiskFunction) (z : ℂ) (w : Circle) :
    boundaryTransport σ f.exp.val z w = f.exp.val (z,w) * boundaryTransport σ f.val z w := by
  exact congrArg (fun L : ChartStein.E →L[ℝ] ℂ => L ((w:ℂ), (Isothermal.angularDrift σ z w:ℂ)*(I*w)))
    (((Complex.hasDerivAt_exp _).comp_hasFDerivAt _ (f.smooth.differentiable (by simp) (z,(w:ℂ))).hasFDerivAt).fderiv)

structure VelocityFactor (σ : ℂ → ℝ) where
  H : DiskFunction
  J : DiskFunction
  inverse : ∀ p, H.val p * J.val p = 1
  even : ∀ z w : ℂ, H.val (z,-w) = H.val (z,w)
  invariant : ∀ z ∈ disk, ∀ w : Circle, boundaryTransport σ (velocity.mul H).val z w = 0

/-- A globally smooth, fibre-holomorphically invertible even factor `H` makes
`w H` into an actual first integral. Its only fibre zero is the simple zero at the origin. -/
theorem exists_velocity_factor {σ : ℂ → ℝ} (simple : SimpleDiskTarget.SimpleMetric σ) (project : HardyProjector)
    (mean : MeanSurjectivity σ) : Nonempty (VelocityFactor σ) := by
  let s (z : ℂ) := (Real.exp (-σ z) : ℂ)
  let t (z : ℂ) := (Real.exp (σ z) : ℂ)
  have hs : ContDiff ℝ ∞ s := Complex.ofRealCLM.contDiff.comp simple.smooth.neg.exp
  have ht : ContDiff ℝ ∞ t := Complex.ofRealCLM.contDiff.comp simple.smooth.exp
  have inv (z : ℂ) : s z * t z = 1 := by
    unfold s t; rw [← Complex.ofReal_mul,← Real.exp_add,neg_add_cancel,Real.exp_zero,Complex.ofReal_one]
  let R (z : ℂ) := Isothermal.raising σ s z 1
  have hR : ContDiff ℝ ∞ R := ScalarGeneralJets.raising_smooth simple.smooth hs _
  let a (z : ℂ) := -(t z ^ 2 * R z)
  have ha : ContDiff ℝ ∞ a := ((ht.pow 2).mul hR).neg
  let g := ScalarGeneralJets.monomial 1 a ha
  have odd (z : ℂ) (_ : z ∈ disk) (w : Circle) : g.val (z,(reverse w:ℂ)) = -g.val (z,w) := by
    simp [g,ScalarGeneralJets.monomial]
  obtain ⟨l,_,parity,dl⟩ := solve_odd simple project mean g odd
  let H := (base s hs).mul l.exp
  let J := (base t ht).mul l.neg.exp
  refine ⟨⟨H,J,?_,?_,?_⟩⟩
  · intro p
    change s p.1 * Complex.exp (l.val p) * (t p.1 * Complex.exp (-l.val p)) = 1
    rw [show s p.1 * Complex.exp (l.val p) * (t p.1 * Complex.exp (-l.val p)) =
      (s p.1 * t p.1) * (Complex.exp (l.val p)*Complex.exp (-l.val p)) by ring, inv, ← Complex.exp_add]
    simp
  · intro z w; simp [H,base,DiskFunction.mul,DiskFunction.exp,parity]
  · intro z hz w
    let q := ScalarGeneralJets.monomial 1 s hs
    have eq : (velocity.mul H).val = (q.mul l.exp).val := by
      funext p; simp [velocity,H,base,q,DiskFunction.mul,ScalarGeneralJets.monomial]; ring
    have dq := ScalarGeneralJets.transport_monomial (σ := σ) hs 0 z w
    change boundaryTransport σ q.val z w = t z * (R z * (w:ℂ)^2 + Isothermal.lowering σ s z 1 * (w:ℂ)^0) at dq
    rw [ScalarGeneralModes.lowering_metric_weight simple.smooth,zero_mul,add_zero] at dq
    rw [eq,X_mul,X_exp,dl z hz,dq]
    change (s z * (w:ℂ)^1) * (l.exp.val (z,w) * (-(t z ^ 2 * R z) * (w:ℂ)^1)) +
      l.exp.val (z,w) * (t z * (R z * (w:ℂ)^2)) = 0
    linear_combination (norm := ring) -(t z * R z * (w:ℂ)^2 * l.exp.val (z,w)) * (inv z)

private theorem X_congr {σ : ℂ → ℝ} (f g : DiskFunction)
    (eq : ∀ z ∈ disk, ∀ w : Circle, f.val (z,w) = g.val (z,w)) {z : ℂ} (hz : z ∈ disk) (w : Circle) :
    boundaryTransport σ f.val z w = boundaryTransport σ g.val z w := by
  let θ := (w:ℂ).arg
  have hw : Circle.exp θ = w := Circle.exp_arg w
  have germ : lifted (trace f) =ᶠ[𝓝 (z,θ)] lifted (trace g) :=
    Filter.mem_of_superset ((isOpen_ball.preimage continuous_fst).mem_nhds hz) (fun x hx => eq _ hx _)
  have Xeq : Isothermal.geodesicX σ (trace f) z w = Isothermal.geodesicX σ (trace g) z w := by
    rw [← hw,PathContinuation.geodesicX_eq_chart_derivative _ _ _ θ ((trace_smooth f).differentiable (by simp) (z,θ)),
      PathContinuation.geodesicX_eq_chart_derivative _ _ _ θ ((trace_smooth g).differentiable (by simp) (z,θ))]
    exact congrArg (fun L : GeodesicFlowExtension.State →L[ℝ] ℂ => L (PathContinuation.chartVector σ (z,θ))) germ.fderiv_eq
  change Isothermal.geodesicX σ (fun y v => f.val (y,(v:ℂ))) z w = Isothermal.geodesicX σ (fun y v => g.val (y,(v:ℂ))) z w at Xeq
  rw [geodesicX_trace f.smooth,geodesicX_trace g.smooth] at Xeq
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)) Xeq

/-- Invert arbitrary smooth functions of the base. A normalized odd-source
solution is divisible by the invariant velocity, with joint smoothness of the quotient. -/
theorem solve_base {σ : ℂ → ℝ} (simple : SimpleDiskTarget.SimpleMetric σ) (project : HardyProjector)
    (mean : MeanSurjectivity σ) (a : ℂ → ℂ) (ha : ContDiff ℝ ∞ a) : ∃ u : DiskFunction,
      ∀ z ∈ disk, ∀ w : Circle, boundaryTransport σ u.val z w = a z := by
  obtain ⟨D⟩ := exists_velocity_factor simple project mean
  let B := velocity.mul D.H
  let f := B.mul (base a ha)
  have odd (z : ℂ) (_ : z ∈ disk) (w : Circle) : f.val (z,(reverse w:ℂ)) = -f.val (z,w) := by
    simp [f,B,DiskFunction.mul,velocity,base,D.even]
  obtain ⟨v,zero,_,dv⟩ := solve_odd simple project mean f odd
  obtain ⟨g,hg⟩ := ScalarGeneral.divide_at_zero v
  let u := g.mul D.J
  have eq (z : ℂ) (hz : z ∈ disk) (w : Circle) : (B.mul u).val (z,w) = v.val (z,w) := by
    have q := hg z hz (w:ℂ) (sphere_subset_closedBall w.property)
    rw [zero z hz,sub_zero] at q
    change ((w:ℂ) * D.H.val (z,w)) * (g.val (z,w)*D.J.val (z,w)) = _
    rw [← q,show ((w:ℂ) * D.H.val (z,w)) * (g.val (z,w)*D.J.val (z,w)) =
      ((w:ℂ)*g.val (z,w)) * (D.H.val (z,w)*D.J.val (z,w)) by ring,D.inverse,mul_one]
  refine ⟨u,?_⟩
  intro z hz w
  have hX := X_congr (σ := σ) _ _ eq hz w
  rw [X_mul, D.invariant z hz, mul_zero, add_zero, dv z hz] at hX
  have hH : D.H.val (z,w) ≠ 0 := left_ne_zero_of_mul_eq_one (D.inverse (z,w))
  exact mul_left_cancel₀ (mul_ne_zero w.coe_ne_zero hH) hX

/-- Scalar zeroth-moment surjectivity and smooth positive Fourier lifting
imply the exact scalar solver for every admissible pencil source. -/
theorem solvable {σ : ℂ → ℝ} (simple : SimpleDiskTarget.SimpleMetric σ) (project : HardyProjector)
    (mean : MeanSurjectivity σ) : ScalarSolvability σ := by
  apply (ScalarGeneral.scalarSolvability_iff σ).mpr
  intro g
  obtain ⟨p,a,ha,_,dp⟩ := solve_modulo_base simple project mean g
  obtain ⟨u,du⟩ := solve_base simple project mean a ha
  refine ⟨p.sub u,?_⟩
  intro z hz w
  have h := congrArg (fun L : ChartStein.E →L[ℝ] ℂ => L ((w:ℂ), (Isothermal.angularDrift σ z w:ℂ)*(I*w)))
    (((p.smooth.differentiable (by simp) (z,(w:ℂ))).hasFDerivAt.sub
    (u.smooth.differentiable (by simp) (z,(w:ℂ))).hasFDerivAt).fderiv)
  change boundaryTransport σ (p.sub u).val z w = boundaryTransport σ p.val z w - boundaryTransport σ u.val z w at h
  rw [h,dp z hz,du z hz,add_sub_cancel_right]

end TransportOkaGrauert.ScalarGeneralMeanSolver
