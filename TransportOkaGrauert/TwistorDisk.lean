import TransportOkaGrauert.Fourier
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.RealDeriv

/-!
# The horizontal twistor equation on a flat velocity disk

In the Euclidean chart its horizontal operator is `w² ∂z + ∂bar_z`.
On the unit tangent bundle this is `w X`. The maximum principle in the
velocity variable thus propagates a boundary transport equation to the
whole closed disk whenever its residual is holomorphic up to the boundary.
-/

noncomputable section

namespace TransportOkaGrauert.TwistorDisk

open Complex Metric Set

/-- The base derivative in the holomorphic base direction. -/
def partialZ (F : ℂ → ℂ → ℂ) (z w : ℂ) : ℂ :=
  fderiv ℝ (fun p => F p w) z 1 / 2 + fderiv ℝ (fun p => F p w) z I / (2 * I)

/-- The base derivative in the antiholomorphic base direction. -/
def partialBarZ (F : ℂ → ℂ → ℂ) (z w : ℂ) : ℂ :=
  fderiv ℝ (fun p => F p w) z 1 / 2 - fderiv ℝ (fun p => F p w) z I / (2 * I)

/-- The horizontal (0,1) twistor vector field in the flat chart. -/
def horizontal (F : ℂ → ℂ → ℂ) (z w : ℂ) : ℂ :=
  w ^ 2 * partialZ F z w + partialBarZ F z w

/-- Restriction of the horizontal operator to unit velocities. -/
theorem horizontal_boundary (F : ℂ → ℂ → ℂ) (z : ℂ) (w : Circle) :
    horizontal F z w = (w : ℂ) * Fourier.flatX (fun p v => F p v) z w := by
  rw [Fourier.flatX, Fourier.linear_split _ w]
  unfold horizontal partialZ partialBarZ
  field_simp [w.coe_ne_zero]


/-- Real differentiation along `z + t w` computes the directional
derivative used by the boundary transport field. -/
theorem line_derivative (F : ℂ → ℂ → ℂ) (z : ℂ) (w : Circle)
    (hF : DifferentiableAt ℝ (fun p => F p w) z) :
    HasDerivAt (fun t : ℝ => F (z + (t : ℂ) * w) w)
      (Fourier.flatX (fun p v => F p v) z w) 0 := by
  have hid : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0 := by
    simpa using (ofRealCLM.hasDerivAt (x := (0 : ℝ)))
  have hdir : HasDerivAt (fun t : ℝ => z + (t : ℂ) * w) (w : ℂ) 0 := by
    simpa using (hid.mul_const (w : ℂ)).const_add z
  have hF' : DifferentiableAt ℝ (fun p => F p w) (z + ((0 : ℝ) : ℂ) * w) := by
    simpa using hF
  simpa [Fourier.flatX, Function.comp_def] using hF'.hasFDerivAt.comp_hasDerivAt 0 hdir

/-- Fiberwise uniqueness on the closed disk, with the boundary parametrized
by the multiplicative unit circle. -/
theorem disk_zero_of_boundary {R : ℂ → ℂ} (hR : DiffContOnCl ℂ R (ball 0 1))
    (hboundary : ∀ w : Circle, R w = 0) {w : ℂ} (hw : w ∈ closedBall 0 1) :
    R w = 0 := by
  have hb : EqOn R (fun _ => 0) (frontier (ball (0 : ℂ) 1)) := by
    intro v hv
    rw [frontier_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)] at hv
    exact hboundary ⟨v, hv⟩
  have hc := eqOn_closure_of_eqOn_frontier isBounded_ball hR diffContOnCl_const hb
  exact hc (by simpa [closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)] using hw)

/-- Entry of the horizontal covariant derivative with disk attenuation `a`. -/
def residual {n : ℕ} (a F : ℂ → ℂ → Matrix (Fin n) (Fin n) ℂ) (z w : ℂ)
    (i j : Fin n) : ℂ :=
  horizontal (fun p v => F p v i j) z w + (a z w * F z w) i j

/-- Transport-to-twistor implication at arbitrary matrix rank. The boundary
coefficient is `w A`, as in Proposition 4.12. On the interior the
hypothesis on the residual is complex differentiability in the fiber. -/
theorem transport_to_disk {n : ℕ} (a F : ℂ → ℂ → Matrix (Fin n) (Fin n) ℂ)
    (A : ℂ → Circle → Matrix (Fin n) (Fin n) ℂ) (z : ℂ)
    (hbase : ∀ (v : Circle) i j, DifferentiableAt ℝ (fun p => F p v i j) z)
    (htrace : ∀ v : Circle, a z v = (v : ℂ) • A z v)
    (htransport : ∀ (v : Circle) i j,
      HasDerivAt (fun t : ℝ => F (z + (t : ℂ) * v) v i j) (-(A z v * F z v) i j) 0)
    (hregular : ∀ i j, DiffContOnCl ℂ (fun v => residual a F z v i j) (ball 0 1))
    {w : ℂ} (hw : w ∈ closedBall 0 1) (i j : Fin n) : residual a F z w i j = 0 := by
  apply disk_zero_of_boundary (hregular i j) _ hw
  intro v
  have hX := (line_derivative (fun p t => F p t i j) z v (hbase v i j)).unique
    (htransport v i j)
  rw [residual, horizontal_boundary, hX, htrace, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]
  ring

end TransportOkaGrauert.TwistorDisk
