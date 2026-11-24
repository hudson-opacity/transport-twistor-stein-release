import TransportOkaGrauert.Isothermal
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic

/-!
# Continuation along a path of attenuations

For an arbitrary spatial vector field `V` in a normed coordinate space, let
`X` be differentiation in direction `V`. Along `t A` a right logarithmic
generator `H` of the frame solves `XH + [tA,H] = -A`. The calculation below
uses symmetry of second derivatives to commute the parameter derivative and
`X`, with no bounded-operator assumption on spatial differentiation.
-/
namespace TransportOkaGrauert.PathContinuation

noncomputable section
open Set

variable {S R : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedRing R] [NormedAlgebra ℝ R]

/-- Spatial and parameter derivatives in a product chart. -/
def spatial (V : S → S) (F : ℝ × S → R) (t : ℝ) (x : S) : R :=
  fderiv ℝ F (t,x) (0, V x)

def timeDerivative (F : ℝ × S → R) (p : ℝ × S) : R := fderiv ℝ F p (1, 0)

private theorem slice_derivative {F : ℝ × S → R} (t : ℝ) (x : S)
    (hF : DifferentiableAt ℝ F (t,x)) :
    HasDerivAt (fun s => F (s,x)) (timeDerivative F (t,x)) t := by
  exact hF.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))

/-- The spatial vector field is independent of the continuation parameter.
The two derivatives commute on a jointly C² frame. -/
theorem transport_time (V : S → S) {F : ℝ × S → R} (hF : ContDiff ℝ 2 F) (t : ℝ) (x : S) :
    HasDerivAt (fun s => spatial V F s x) (spatial V (timeDerivative F) t x) t := by
  let ev (v : ℝ × S) := ContinuousLinearMap.apply ℝ R v
  have hd : DifferentiableAt ℝ (fderiv ℝ F) (t,x) :=
    ((hF.fderiv_right (m := 1) (by decide)).differentiable one_ne_zero).differentiableAt
  have hdir (v : ℝ × S) : HasFDerivAt (fun p => fderiv ℝ F p v)
      ((ev v).comp (fderiv ℝ (fderiv ℝ F) (t,x))) (t,x) :=
    (ev v).hasFDerivAt.comp _ hd.hasFDerivAt
  have h := slice_derivative t x (hdir (0, V x)).differentiableAt
  have hsym := hF.contDiffAt.isSymmSndFDerivAt (x := (t,x)) (by simp)
  unfold spatial timeDerivative at h ⊢
  rw [(hdir (0, V x)).fderiv] at h
  rw [(hdir (1,0)).fderiv]
  convert h using 1
  exact hsym.eq _ _

/-- The derivative at a fixed time agrees with the ordinary spatial derivative
of the corresponding time slice, including at parameter endpoints. -/
theorem spatial_eq_slice (V : S → S) {F : ℝ × S → R} (t : ℝ) (x : S)
    (hF : DifferentiableAt ℝ F (t,x)) :
    spatial V F t x = fderiv ℝ (fun y => F (t,y)) x (V x) := by
  have h := hF.hasFDerivAt.comp x ((hasFDerivAt_const t x).prodMk (hasFDerivAt_id x))
  rw [show (fun y => F (t,y)) = F ∘ (fun y => (t,y)) by rfl, h.fderiv]
  rfl

/-- Product rule in the spatial direction keeps the order of its two factors. -/
private theorem spatial_mul (V : S → S) {H F : ℝ × S → R} (t : ℝ) (x : S)
    (hH : DifferentiableAt ℝ H (t,x)) (hF : DifferentiableAt ℝ F (t,x)) :
    spatial V (fun p => H p * F p) t x =
      spatial V H t x * F (t,x) + H (t,x) * spatial V F t x := by
  unfold spatial
  rw [fderiv_fun_mul' hH hF]
  exact add_comm _ _

/-- Error in the transport equation for the attenuation `t A`. -/
def residual (V : S → S) (A : S → R) (F : ℝ × S → R) (t : ℝ) (x : S) :=
  spatial V F t x + (t • A x) * F (t,x)

/-- Exact homogeneous ODE for the transport error. The generator is found
from the linearized equation, independently of the unknown frame. -/
theorem residual_derivative (V : S → S) (A : S → R) (H F : ℝ × S → R)
    (hF : ContDiff ℝ 2 F) (hH : Differentiable ℝ H)
    (t : ℝ) (x : S)
    (evolution : ∀ y, timeDerivative F (t,y) = H (t,y) * F (t,y))
    (generator : spatial V H t x + (t • A x) * H (t,x) - H (t,x) * (t • A x) = -(A x)) :
    HasDerivAt (fun s => residual V A F s x) (H (t,x) * residual V A F t x) t := by
  have hf := hF.differentiable (by decide : (2 : WithTop ℕ∞) ≠ 0)
  have htime := slice_derivative t x (hf (t,x))
  rw [evolution] at htime
  have hs := transport_time V hF t x
  have hd : DifferentiableAt ℝ (fderiv ℝ F) (t,x) :=
    ((hF.fderiv_right (m := 1) (by decide)).differentiable one_ne_zero).differentiableAt
  have hdt : DifferentiableAt ℝ (timeDerivative F) (t,x) :=
    (ContinuousLinearMap.apply ℝ R ((1 : ℝ), (0 : S))).differentiableAt.comp _ hd
  rw [spatial_eq_slice V t x hdt, funext evolution, ← spatial_eq_slice V (F := fun p => H p * F p) t x ((hH _).mul (hf _)),
    spatial_mul V t x (hH _) (hf _)] at hs
  have ha : HasDerivAt (fun s : ℝ => s • A x) (A x) t := by
    simpa using (hasDerivAt_id t).smul_const (A x)
  convert hs.add (ha.mul htime) using 1
  unfold residual
  have hgen : spatial V H t x = -(A x) - (t • A x) * H (t,x) + H (t,x) * (t • A x) := by
    rw [← generator]
    abel
  rw [hgen]
  noncomm_ring

/-- Propagation on the whole closed parameter interval from F(0,x) = 1.
A continuous-in-time generator is bounded at each fixed spatial point, so
ordinary Grönwall uniqueness forces the transport error to stay zero. -/
theorem residual_eq_zero_on_unitInterval (V : S → S) (A : S → R) (H F : ℝ × S → R)
    (hF : ContDiff ℝ 2 F) (hH : Differentiable ℝ H)
    (evolution : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, timeDerivative F (t,x) = H (t,x) * F (t,x))
    (generator : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, spatial V H t x + (t • A x) * H (t,x) -
      H (t,x) * (t • A x) = -(A x))
    (initial : ∀ x, F (0,x) = 1) (x : S) :
    ∀ t ∈ Icc (0 : ℝ) 1, residual V A F t x = 0 := by
  have hcont : Continuous (fun t : ℝ => H (t,x)) :=
    hH.continuous.comp (continuous_id.prodMk continuous_const)
  obtain ⟨u, _, hu⟩ := isCompact_Icc.exists_isMaxOn
    (nonempty_Icc.mpr (zero_le_one : (0 : ℝ) ≤ 1)) hcont.norm.continuousOn
  have hder (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :=
    residual_derivative V A H F hF hH t x (evolution t ht) (generator t ht x)
  apply eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
    (f' := fun t => H (t,x) * residual V A F t x) (K := ‖H (u,x)‖)
  · exact fun t ht => (hder t ht).continuousAt.continuousWithinAt
  · intro t ht
    exact (hder t ⟨ht.1, ht.2.le⟩).hasDerivWithinAt
  · simp only [residual, zero_smul, zero_mul, add_zero]
    rw [spatial_eq_slice V 0 x (hF.differentiable (by decide) _), funext initial]
    simp
  · intro t ht
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
      (hu ⟨ht.1, ht.2.le⟩) (norm_nonneg _))

/-- At t = 1 the frame obtained by parameter evolution solves the prescribed
spatial transport equation. -/
theorem endpoint_transport (V : S → S) (A : S → R) (H F : ℝ × S → R)
    (hF : ContDiff ℝ 2 F) (hH : Differentiable ℝ H)
    (evolution : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, timeDerivative F (t,x) = H (t,x) * F (t,x))
    (generator : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, spatial V H t x + (t • A x) * H (t,x) -
      H (t,x) * (t • A x) = -(A x))
    (initial : ∀ x, F (0,x) = 1) (x : S) :
    fderiv ℝ (fun y => F (1,y)) x (V x) + A x * F (1,x) = 0 := by
  have h := residual_eq_zero_on_unitInterval V A H F hF hH evolution generator initial x 1 (by simp)
  simpa [residual, spatial_eq_slice V 1 x (hF.differentiable (by decide) _)] using h

/-- The velocity of the conformal geodesic flow on the real angular cover. -/
def chartVector (lam : ℂ → ℝ) (p : ℂ × ℝ) : ℂ × ℝ :=
  Real.exp (-lam p.1) • ((Circle.exp p.2 : ℂ), Isothermal.angularDrift lam p.1 (Circle.exp p.2))

/-- The derivative in the lifted vector is exactly the previously defined
geodesic operator. The angle is lifted to ℝ only to take an ordinary
Fréchet derivative. -/
theorem geodesicX_eq_chart_derivative (lam : ℂ → ℝ) (f : ℂ → Circle → ℂ) (z : ℂ) (θ : ℝ)
    (hd : DifferentiableAt ℝ (fun p : ℂ × ℝ => f p.1 (Circle.exp p.2)) (z,θ)) :
    Isothermal.geodesicX lam f z (Circle.exp θ) =
      fderiv ℝ (fun p : ℂ × ℝ => f p.1 (Circle.exp p.2)) (z,θ) (chartVector lam (z,θ)) := by
  let g (p : ℂ × ℝ) := f p.1 (Circle.exp p.2)
  let L := fderiv ℝ g (z,θ)
  let w := Circle.exp θ
  let d := Isothermal.angularDrift lam z w
  have hbase : Fourier.flatX f z w = L (w,0) := by
    have e : HasFDerivAt (fun p : ℂ => (p, θ)) ((ContinuousLinearMap.id ℝ ℂ).prod 0) z :=
      (hasFDerivAt_id z).prodMk (hasFDerivAt_const θ z)
    have h := hd.hasFDerivAt.comp z e
    exact congrArg (fun u : ℂ →L[ℝ] ℂ => u (w : ℂ)) h.fderiv
  have hangle : Isothermal.vertical f z w = L (0,1) := by
    have hg : DifferentiableAt ℝ g (z, θ + 0) := by simpa [g] using hd
    have e : HasDerivAt (fun t : ℝ => (z, θ+t)) ((0 : ℂ), (1 : ℝ)) 0 :=
      (hasDerivAt_const (0 : ℝ) z).prodMk ((hasDerivAt_id (0 : ℝ)).const_add θ)
    have h := hg.hasFDerivAt.comp_hasDerivAt (0 : ℝ) e
    simpa only [g, Function.comp_def, id_eq, Circle.exp_add, add_zero, Isothermal.vertical, w, L]
      using h.deriv
  have hs : ((w : ℂ), d) = ((w : ℂ), (0 : ℝ)) + d • ((0 : ℂ), (1 : ℝ)) := by simp
  change (Real.exp (-lam z) : ℂ) * (Fourier.flatX f z w +
    (d : ℂ) * Isothermal.vertical f z w) = L (Real.exp (-lam z) • ((w : ℂ),d))
  rw [hbase, hangle, hs, map_smul, map_add, map_smul]
  rfl

open scoped Matrix.Norms.Operator

/-- At any rank the matrix-valued directional equation in the continuation
theorem is equivalent to the chart's entrywise transport equations. -/
theorem chart_matrix_transport_iff {n : ℕ} (lam : ℂ → ℝ)
    (A F : ℂ → Circle → Matrix (Fin n) (Fin n) ℂ) (z : ℂ) (θ : ℝ)
    (hF : DifferentiableAt ℝ (fun p : ℂ × ℝ => F p.1 (Circle.exp p.2)) (z,θ)) :
    fderiv ℝ (fun p : ℂ × ℝ => F p.1 (Circle.exp p.2)) (z,θ) (chartVector lam (z,θ)) +
      A z (Circle.exp θ) * F z (Circle.exp θ) = 0 ↔
    ∀ i j, Isothermal.geodesicX lam (fun x v => F x v i j) z (Circle.exp θ) +
      (A z (Circle.exp θ) * F z (Circle.exp θ)) i j = 0 := by
  let g (p : ℂ × ℝ) := F p.1 (Circle.exp p.2)
  have he (i j : Fin n) : Isothermal.geodesicX lam (fun x v => F x v i j) z (Circle.exp θ) =
      fderiv ℝ g (z,θ) (chartVector lam (z,θ)) i j := by
    let ev : Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℂ :=
      ⟨Matrix.entryLinearMap ℝ ℂ i j, (continuous_apply j).comp (continuous_apply i)⟩
    have h := ev.hasFDerivAt.comp (z,θ) hF.hasFDerivAt
    rw [geodesicX_eq_chart_derivative lam _ z θ h.differentiableAt]
    exact congrArg (fun L : (ℂ × ℝ) →L[ℝ] ℂ => L (chartVector lam (z,θ))) h.fderiv
  constructor
  · intro h i j
    rw [he]
    exact congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M i j) h
  · intro h
    ext i j
    have hij := h i j
    rw [he i j] at hij
    exact hij

end
end TransportOkaGrauert.PathContinuation
