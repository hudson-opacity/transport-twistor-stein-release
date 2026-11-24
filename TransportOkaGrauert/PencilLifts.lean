import TransportOkaGrauert.ChartCorrespondence

/-!
# Scalar transport solvability gives holomorphic pencil and interpolation functions

This reduction works with the concrete curved CR equations and actual real
directional derivatives on the circle. Its analytic input, `ScalarSolvability`,
is the unattenuated right-inverse theorem together with a smooth fibre
extension. It is an explicit hypothesis, not an axiom of this project.
-/
namespace TransportOkaGrauert.PencilLifts
noncomputable section
open Set Complex Metric ChartStein ChartCorrespondence
open scoped ContDiff ComplexConjugate

abbrev disk := ball (0:ℂ) 1

/-- A disk function smooth in the physical coordinates and holomorphic on each
open velocity disk. Only its values on the bundle over the disk are used. -/
structure DiskFunction where
  val : E → ℂ
  smooth : ContDiff ℝ ∞ val
  fibre : ∀ z ∈ disk, DifferentiableOn ℂ (fun w => val (z,w)) disk

def DiskFunction.mul (f g : DiskFunction) : DiskFunction where
  val p := f.val p * g.val p
  smooth := f.smooth.mul g.smooth
  fibre z hz := (f.fibre z hz).mul (g.fibre z hz)

def DiskFunction.sub (f g : DiskFunction) : DiskFunction where
  val p := f.val p - g.val p
  smooth := f.smooth.sub g.smooth
  fibre z hz := (f.fibre z hz).sub (g.fibre z hz)

def DiskFunction.neg (f : DiskFunction) : DiskFunction where
  val p := -f.val p
  smooth := f.smooth.neg
  fibre z hz := (f.fibre z hz).neg

def DiskFunction.exp (f : DiskFunction) : DiskFunction where
  val p := Complex.exp (f.val p)
  smooth := f.smooth.cexp
  fibre z hz := (f.fibre z hz).cexp

def velocity : DiskFunction where
  val := Prod.snd
  smooth := contDiff_snd
  fibre _ _ := differentiableOn_id

abbrev TraceRHS := ℂ → Circle → ℂ

/-- Having circle modes ≥ −1, expressed through existence of an actual smooth
holomorphic extension of the trace multiplied by its velocity. -/
def ShiftExtends (rhs : TraceRHS) : Prop :=
  ∃ f : DiskFunction, ∀ z ∈ disk, ∀ w : Circle, f.val (z,w) = (w:ℂ) * rhs z w

/-- Unscaled geodesic differentiation differs from X by a positive
base-dependent scalar. This input specifies a solution for each admissible
source and does not postulate a pencil, local coordinates, or hulls. -/
def ScalarSolvability (σ : ℂ → ℝ) : Prop :=
  ∀ rhs : TraceRHS, ShiftExtends rhs → ∃ f : DiskFunction,
    ∀ z ∈ disk, ∀ w : Circle, boundaryTransport σ f.val z w = rhs z w

theorem shifted_disk_function (f : DiskFunction) :
    ShiftExtends (fun z w => f.val (z,w)) :=
  ⟨velocity.mul f, fun _ _ _ => rfl⟩

private theorem transport_mul (σ : ℂ → ℝ) (f g : DiskFunction) (z : ℂ) (w : Circle) :
    boundaryTransport σ (f.mul g).val z w =
    f.val (z,w) * boundaryTransport σ g.val z w + g.val (z,w) * boundaryTransport σ f.val z w := by
  have h := ((f.smooth.differentiable (by simp) (z,(w:ℂ))).hasFDerivAt.mul
    (g.smooth.differentiable (by simp) (z,(w:ℂ))).hasFDerivAt).fderiv
  exact congrArg (fun L : E →L[ℝ] ℂ => L ((w:ℂ),(Isothermal.angularDrift σ z w : ℂ)*(I*w))) h

private theorem transport_sub (σ : ℂ → ℝ) (f g : DiskFunction) (z : ℂ) (w : Circle) :
    boundaryTransport σ (f.sub g).val z w =
    boundaryTransport σ f.val z w - boundaryTransport σ g.val z w := by
  have h := ((f.smooth.differentiable (by simp) (z,(w:ℂ))).hasFDerivAt.sub
    (g.smooth.differentiable (by simp) (z,(w:ℂ))).hasFDerivAt).fderiv
  exact congrArg (fun L : E →L[ℝ] ℂ => L ((w:ℂ),(Isothermal.angularDrift σ z w : ℂ)*(I*w))) h

private theorem transport_exp (σ : ℂ → ℝ) (f : DiskFunction) (z : ℂ) (w : Circle) :
    boundaryTransport σ f.exp.val z w =
    Complex.exp (f.val (z,w)) * boundaryTransport σ f.val z w := by
  have h := ((Complex.hasDerivAt_exp (f.val (z,w))).comp_hasFDerivAt (z,(w:ℂ))
    (f.smooth.differentiable (by simp) (z,(w:ℂ))).hasFDerivAt).fderiv
  exact congrArg (fun L : E →L[ℝ] ℂ => L ((w:ℂ),(Isothermal.angularDrift σ z w : ℂ)*(I*w))) h

/-- The two uncorrected polynomials q and m obey transport equations with
sources of precisely the admissible degrees. Solving two scalar equations
produces genuine holomorphic functions F and G with F=exp(ℓ)q and G=m−uF.
In particular F keeps the entire zero set of q, including the boundary, and G
interpolates m on it. -/
theorem correct_pencil_with_trace {σ : ℂ → ℝ} (solve : ScalarSolvability σ)
    (q m b : DiskFunction) (a : TraceRHS) (ha : ShiftExtends a)
    (hq : ∀ z ∈ disk, ∀ w : Circle, boundaryTransport σ q.val z w = -a z w * q.val (z,w))
    (hm : ∀ z ∈ disk, ∀ w : Circle, boundaryTransport σ m.val z w = b.val (z,w) * q.val (z,w)) :
    ∃ l u : DiskFunction,
      HolOn σ disk (l.exp.mul q).val ∧ HolOn σ disk (m.sub (u.mul (l.exp.mul q))).val ∧
      ∀ z ∈ disk, ∀ w : Circle, boundaryTransport σ (l.exp.mul q).val z w = 0 := by
  obtain ⟨l, hl⟩ := solve a ha
  let F := l.exp.mul q
  have hF : ∀ z ∈ disk, ∀ w : Circle, boundaryTransport σ F.val z w = 0 := by
    intro z hz w
    rw [show F = l.exp.mul q from rfl, transport_mul, transport_exp, hl z hz, hq z hz]
    change Complex.exp _ * _ + _ * (Complex.exp _ * _) = 0
    ring
  let rhs := b.mul l.neg.exp
  obtain ⟨u, hu⟩ := solve (fun z w => rhs.val (z,w)) (shifted_disk_function rhs)
  let G := m.sub (u.mul F)
  have hG : ∀ z ∈ disk, ∀ w : Circle, boundaryTransport σ G.val z w = 0 := by
    intro z hz w
    rw [show G = m.sub (u.mul F) from rfl, transport_sub, transport_mul, hm z hz, hF z hz, hu z hz]
    change _ - (_ * 0 + (Complex.exp _ * _) * (_ * Complex.exp (-_))) = 0
    rw [Complex.exp_neg]
    field_simp
    ring
  have prop (f : DiskFunction)
      (h : ∀ z ∈ disk, ∀ w : Circle, boundaryTransport σ f.val z w = 0) : HolOn σ disk f.val := by
    apply holOn_of_firstIntegral f.smooth isOpen_ball f.fibre
    intro z hz w
    rw [geodesicX_trace f.smooth, h z hz, mul_zero]
  exact ⟨l,u,prop F hF,prop G hG,hF⟩

theorem correct_pencil {σ : ℂ → ℝ} (solve : ScalarSolvability σ)
    (q m b : DiskFunction) (a : TraceRHS) (ha : ShiftExtends a)
    (hq : ∀ z ∈ disk, ∀ w : Circle, boundaryTransport σ q.val z w = -a z w * q.val (z,w))
    (hm : ∀ z ∈ disk, ∀ w : Circle, boundaryTransport σ m.val z w = b.val (z,w) * q.val (z,w)) :
    ∃ l u : DiskFunction,
      HolOn σ disk (l.exp.mul q).val ∧ HolOn σ disk (m.sub (u.mul (l.exp.mul q))).val := by
  obtain ⟨l,u,hF,hG,_⟩ := correct_pencil_with_trace solve q m b a ha hq hm
  exact ⟨l,u,hF,hG⟩

end
end TransportOkaGrauert.PencilLifts
