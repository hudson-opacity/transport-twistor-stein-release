import TransportOkaGrauert.ChartStein
import TransportOkaGrauert.TwistorDisk
import Mathlib.Analysis.Complex.Conformal
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# A smooth fibre extension of a first integral satisfies the curved twistor PDE

The scalar horizontal residual is holomorphic in velocity. We derive this,
including holomorphicity of the base derivatives, by symmetry of the real
second differential. The unit-circle trace equation then propagates to the
disk by the maximum principle. The conformal factor may vary.
-/
namespace TransportOkaGrauert.ChartCorrespondence
noncomputable section
open Set Complex Metric Filter ChartStein
open scoped ContDiff Topology ComplexConjugate

def slope (F : E → ℂ) (d : E) (p : E) : ℂ := fderiv ℝ F p d

def VerticalCR (F : E → ℂ) (p : E) : Prop :=
  slope F (0,I) p = I * slope F (0,1) p

def residual (σ : ℂ → ℝ) (F : E → ℂ) (z w : ℂ) : ℂ :=
  w^2 * (slope F (1,0) (z,w) - I * slope F (I,0) (z,w)) +
  (slope F (1,0) (z,w) + I * slope F (I,0) (z,w)) -
  connectionCoefficient σ (z,w) * slope F (0,1) (z,w)

private theorem slope_smooth {F : E → ℂ} (hs : ContDiff ℝ ∞ F) (d : E) :
    ContDiff ℝ ∞ (slope F d) :=
  (hs.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

private theorem derivative_slope {F : E → ℂ} (hs : ContDiff ℝ ∞ F) (p d v : E) :
    fderiv ℝ (slope F d) p v = fderiv ℝ (fderiv ℝ F) p v d := by
  have h := (hs.fderiv_right (m := ∞) (by simp)).differentiable (by simp)
  unfold slope
  rw [fderiv_clm_apply h.differentiableAt (differentiableAt_const _)]
  simp

private theorem fibre_derivative {f : E → ℂ} (z w a : ℂ) (hf : DifferentiableAt ℝ f (z,w)) :
    fderiv ℝ (fun u => f (z,u)) w a = fderiv ℝ f (z,w) (0,a) := by
  have hd := hf.hasFDerivAt.comp w ((hasFDerivAt_const z w).prodMk (hasFDerivAt_id w))
  exact congrArg (fun L : ℂ →L[ℝ] ℂ => L a) hd.fderiv

/-- Complex differentiability in the velocity variable propagates to every
real directional derivative, including horizontal base derivatives. -/
theorem slope_fibre_holomorphic {F : E → ℂ} (hs : ContDiff ℝ ∞ F)
    {O : Set E} (hO : IsOpen O) (hv : ∀ p ∈ O, VerticalCR F p)
    {z w : ℂ} (hp : (z,w) ∈ O) (d : E) :
    DifferentiableAt ℂ (fun u => slope F d (z,u)) w := by
  let p : E := (z,w)
  have symm := hs.contDiffAt.isSymmSndFDerivAt (x := p) (by simp; exact WithTop.coe_le_coe.mpr le_top)
  have sw (a b : E) : fderiv ℝ (slope F a) p b = fderiv ℝ (slope F b) p a := by
    simp only [derivative_slope hs]
    exact symm b a
  have ev : slope F (0,I) =ᶠ[𝓝 p] fun q => I * slope F (0,1) q :=
    Filter.mem_of_superset (hO.mem_nhds hp) (fun q hq => hv q hq)
  have hd : fderiv ℝ (slope F (0,I)) p d = I * fderiv ℝ (slope F (0,1)) p d := by
    rw [ev.fderiv_eq]
    exact congrArg (fun L : E →L[ℝ] ℂ => L d)
      ((((slope_smooth hs _).differentiable (by simp) p).hasFDerivAt.const_mul I).fderiv)
  have hdiff := (slope_smooth hs d).differentiable (by simp)
  apply differentiableAt_complex_iff_differentiableAt_real.mpr
  constructor
  · exact (hdiff p).comp w ((differentiableAt_const z).prodMk differentiableAt_id)
  · simp only [smul_eq_mul, fibre_derivative z w _ (hdiff p)]
    change fderiv ℝ (slope F d) p (0,I) = I * fderiv ℝ (slope F d) p (0,1)
    rw [sw d (0,I), sw d (0,1)]
    exact hd

private theorem coefficient_fibre (σ : ℂ → ℝ) (z : ℂ) :
    Differentiable ℂ (fun w => connectionCoefficient σ (z,w)) := by
  dsimp [connectionCoefficient]
  fun_prop

theorem residual_fibre {F : E → ℂ} (hs : ContDiff ℝ ∞ F)
    {U : Set ℂ} (hU : IsOpen U) (hv : ∀ z ∈ U, ∀ w ∈ ball (0:ℂ) 1, VerticalCR F (z,w))
    (σ : ℂ → ℝ) {z : ℂ} (hz : z ∈ U) :
    DiffContOnCl ℂ (residual σ F z) (ball 0 1) := by
  have hO := hU.prod (isOpen_ball (x := (0:ℂ)) (ε := 1))
  constructor
  · intro w hw
    have h (d : E) := slope_fibre_holomorphic hs hO (fun p hp => hv _ hp.1 _ hp.2)
      (z := z) (w := w) ⟨hz, hw⟩ d
    apply DifferentiableAt.differentiableWithinAt
    unfold residual
    exact (((differentiableAt_id.pow 2).mul ((h _).sub ((h _).const_mul I))).add
      ((h _).add ((h _).const_mul I))).sub (((coefficient_fibre σ z) w).mul (h _))
  · have h (d : E) : Continuous (fun w => slope F d (z,w)) :=
      (slope_smooth hs d).continuous.comp (continuous_const.prodMk continuous_id)
    apply Continuous.continuousOn
    unfold residual
    exact (((continuous_id.pow 2).mul ((h _).sub (continuous_const.mul (h _)))).add
      ((h _).add (continuous_const.mul (h _)))).sub ((coefficient_fibre σ z).continuous.mul (h _))

/-- The real derivative of the disk extension in its geodesic direction
on the unit bundle, without the positive conformal speed factor. -/
def boundaryTransport (σ : ℂ → ℝ) (F : E → ℂ) (z : ℂ) (w : Circle) : ℂ :=
  slope F ((w : ℂ), (Isothermal.angularDrift σ z w : ℂ) * (I * w)) (z,w)

private theorem split_base (D : E →L[ℝ] ℂ) (w : ℂ) :
    D (w,0) = (w.re : ℂ) * D (1,0) + (w.im : ℂ) * D (I,0) := by
  have e : (w,0) = w.re • ((1,0):E) + w.im • ((I,0):E) := by
    ext <;> simp [Complex.real_smul]
  rw [e, map_add, map_smul, map_smul]
  rfl

private theorem split_fibre (D : E →L[ℝ] ℂ) (w : ℂ) (h : D (0,I) = I * D (0,1)) :
    D (0,w) = w * D (0,1) := by
  have e : (0,w) = w.re • ((0,1):E) + w.im • ((0,I):E) := by
    ext <;> simp [Complex.real_smul]
  conv_lhs => rw [e, map_add, map_smul, map_smul, h]
  simp only [Complex.real_smul]
  linear_combination -((D (0,1)) * (Complex.re_add_im w).symm)

theorem residual_on_circle {σ : ℂ → ℝ} {F : E → ℂ} (z : ℂ) (w : Circle)
    (hv : VerticalCR F (z,w)) :
    residual σ F z w = 2 * (w : ℂ) * boundaryTransport σ F z w := by
  let D := fderiv ℝ F (z,(w:ℂ))
  have hunit : (w : ℂ) * conj (w : ℂ) = 1 := by
    rw [← Circle.coe_inv_eq_conj, Circle.coe_inv, mul_inv_cancel₀ w.coe_ne_zero]
  have hre : 2 * (w : ℂ) * ((w : ℂ).re : ℂ) = (w : ℂ)^2 + 1 := by
    rw [Complex.re_eq_add_conj]; linear_combination hunit
  have him : 2 * (w : ℂ) * ((w : ℂ).im : ℂ) = I * (1 - (w : ℂ)^2) := by
    apply mul_left_cancel₀ Complex.I_ne_zero
    calc
      I * (2 * (w : ℂ) * ((w : ℂ).im : ℂ)) =
          2 * (w : ℂ) * (((w : ℂ).re : ℂ) + ((w : ℂ).im : ℂ) * I) -
            2 * (w : ℂ) * ((w : ℂ).re : ℂ) := by ring
      _ = _ := by rw [Complex.re_add_im, hre]; linear_combination - (1 - (w : ℂ)^2) * Complex.I_sq
  have es (a b : ℂ) : D (a,b) = D (a,0) + D (0,b) := by rw [← map_add]; simp
  unfold boundaryTransport residual slope
  change _ = 2 * (w : ℂ) * D (_, _)
  conv_rhs => rw [es (w : ℂ) _, split_base, split_fibre D _ hv]
  change _ = 2 * (w : ℂ) * (((w : ℂ).re : ℂ) * D (1,0) +
    ((w : ℂ).im : ℂ) * D (I,0) + _)
  unfold connectionCoefficient Isothermal.angularDrift
  simp only [Complex.ofReal_sub, Complex.ofReal_mul]
  -- The two real components of a unit complex number yield the trace identity.
  linear_combination
    -(D (1,0) + I * (w : ℂ) * (fderiv ℝ σ z I : ℂ) * D (0,1)) * hre -
    (D (I,0) - I * (w : ℂ) * (fderiv ℝ σ z 1 : ℂ) * D (0,1)) * him +
    ((w : ℂ) * (fderiv ℝ σ z 1 : ℂ) * D (0,1) * (1 - (w : ℂ)^2)) * Complex.I_sq

/-- Given the smooth fibrewise-holomorphic disk extension, actual geodesic
invariance of its unit-circle trace forces the curved horizontal equation
throughout the open disk. -/
theorem holOn_of_trace {σ : ℂ → ℝ} {F : E → ℂ} (hs : ContDiff ℝ ∞ F)
    {U : Set ℂ} (hU : IsOpen U)
    (hv : ∀ z ∈ U, ∀ w ∈ closedBall (0:ℂ) 1, VerticalCR F (z,w))
    (hX : ∀ z ∈ U, ∀ w : Circle, boundaryTransport σ F z w = 0) :
    HolOn σ U F := by
  intro p
  let z := p.val.1.val
  let w := p.val.2.val
  have hz : z ∈ U := p.property.1
  have hw : w ∈ closedBall (0:ℂ) 1 := p.val.2.property
  have hr : residual σ F z w = 0 := TwistorDisk.disk_zero_of_boundary
    (residual_fibre hs hU (fun a ha b hb => hv a ha b (ball_subset_closedBall hb)) σ hz)
    (fun v => by rw [residual_on_circle _ v (hv z hz v (sphere_subset_closedBall v.property)), hX z hz, mul_zero]) hw
  exact ⟨hs.contDiffAt, hv z hz w hw, hr⟩

/-- The trace direction above is precisely the chart geodesic vector field
already used to define transport in this project, up to its positive speed. -/
theorem geodesicX_trace {F : E → ℂ} (hs : ContDiff ℝ ∞ F) (σ : ℂ → ℝ)
    (z : ℂ) (w : Circle) :
    Isothermal.geodesicX σ (fun a v => F (a,(v:ℂ))) z w =
      (Real.exp (-σ z) : ℂ) * boundaryTransport σ F z w := by
  let D := fderiv ℝ F (z,(w:ℂ))
  have h := (hs.differentiable (by simp) (z,(w:ℂ))).hasFDerivAt
  have hb := (show HasFDerivAt F D ((fun a : ℂ => (a,(w:ℂ))) z) from h).comp z
    ((hasFDerivAt_id (𝕜 := ℝ) z).prodMk (hasFDerivAt_const (w:ℂ) z))
  have base : Fourier.flatX (fun a (v:Circle) => F (a,(v:ℂ))) z w = D ((w:ℂ),0) :=
    congrArg (fun L : ℂ →L[ℝ] ℂ => L w) hb.fderiv
  have ray : HasDerivAt (fun t : ℝ => (w : ℂ) * Complex.exp ((t:ℂ)*I))
      (I*(w:ℂ)) 0 := by
    simpa [mul_comm] using
      ((((Complex.ofRealCLM.hasDerivAt (x := (0:ℝ))).mul_const I).cexp).const_mul (w:ℂ))
  have hpair : HasDerivAt (fun t : ℝ => (z,(w:ℂ)*Complex.exp ((t:ℂ)*I)))
      ((0,I*(w:ℂ)):E) 0 := (hasDerivAt_const (0:ℝ) z).prodMk ray
  have hp : (z, (w:ℂ)*Complex.exp (((0:ℝ):ℂ)*I)) = (z,(w:ℂ)) := by simp
  have hF : HasFDerivAt F D (z,(w:ℂ)*Complex.exp (((0:ℝ):ℂ)*I)) := hp.symm ▸ h
  have vert : Isothermal.vertical (fun a (v:Circle) => F (a,(v:ℂ))) z w = D (0,I*(w:ℂ)) :=
    (show HasDerivAt (fun t : ℝ => F (z,(w:ℂ)*Complex.exp ((t:ℂ)*I)))
      (D (0,I*(w:ℂ))) 0 from hF.comp_hasDerivAt 0 hpair).deriv
  let a := Isothermal.angularDrift σ z w
  have es : ((w:ℂ), (a:ℂ)*(I*(w:ℂ))) = ((w:ℂ),0) + a • ((0,I*(w:ℂ)):E) := by
    ext <;> simp [Complex.real_smul]
  unfold Isothermal.geodesicX
  rw [base, vert]
  change _ = _ * D ((w:ℂ), (a:ℂ)*(I*(w:ℂ)))
  rw [es, map_add, map_smul]; rfl

/-- For a jointly smooth disk extension, fibrewise complex differentiability
in the open disk and actual geodesic invariance on the unit circle imply both
twistor CR equations. No horizontal residual regularity is assumed. -/
theorem holOn_of_firstIntegral {σ : ℂ → ℝ} {F : E → ℂ} (hs : ContDiff ℝ ∞ F)
    {U : Set ℂ} (hU : IsOpen U)
    (hf : ∀ z ∈ U, DifferentiableOn ℂ (fun w => F (z,w)) (ball 0 1))
    (hX : ∀ z ∈ U, ∀ w : Circle, Isothermal.geodesicX σ (fun a v => F (a,(v:ℂ))) z w = 0) :
    HolOn σ U F := by
  apply holOn_of_trace hs hU
  · intro z hz
    have sc (d : E) : Continuous (fun w : ℂ => slope F d (z,w)) :=
      (slope_smooth hs d).continuous.comp (continuous_const.prodMk continuous_id)
    have closed : IsClosed {w : ℂ | VerticalCR F (z,w)} :=
      isClosed_eq (sc _) (continuous_const.mul (sc _))
    have inc : ball (0:ℂ) 1 ⊆ {w : ℂ | VerticalCR F (z,w)} := by
      intro w hw
      have eq := (differentiableAt_complex_iff_differentiableAt_real.mp
        ((hf z hz w hw).differentiableAt (isOpen_ball.mem_nhds hw))).2
      simpa only [smul_eq_mul, fibre_derivative _ _ _ (hs.differentiable (by simp) _)] using eq
    have all := closure_minimal inc closed
    rw [closure_ball (0:ℂ) (by norm_num : (1:ℝ) ≠ 0)] at all
    exact all
  · intro z hz w
    have h := hX z hz w
    rw [geodesicX_trace hs] at h
    exact (mul_eq_zero.mp h).resolve_left (by exact_mod_cast Real.exp_ne_zero _)

end
end TransportOkaGrauert.ChartCorrespondence
