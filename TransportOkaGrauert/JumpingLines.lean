import TransportOkaGrauert.BoundaryModes
import TransportOkaGrauert.TwistorDisk

/-!
# A geodesic first integral with an exceptional Birkhoff fibre

The exterior coordinate is `q = w⁻¹`, so normalization at infinity means
evaluation at `q = 0`. The interior and exterior factors below extend as
polynomial matrices over the whole of their respective velocity charts.
-/

noncomputable section

namespace TransportOkaGrauert.JumpingLines

open scoped ComplexConjugate ContDiff Matrix

abbrev Mat := Matrix (Fin 2) (Fin 2) ℂ

/-- The off-diagonal entry is constant along each oriented Euclidean line. -/
def W (z w : ℂ) : Mat := !![w, FlatScalar.firstIntegral z w; 0, w⁻¹]

theorem W_det (z : ℂ) {w : ℂ} (hw : w ≠ 0) : (W z w).det = 1 := by
  simp [W, Matrix.det_fin_two, hw]

/-- Constancy along the full straight line, for every circle velocity. -/
theorem W_advance (z : ℂ) (v : Circle) (t : ℝ) : W (z + t * v) v = W z v := by
  have hu : (v : ℂ) * conj (v : ℂ) = 1 := by
    rw [← Circle.coe_inv_eq_conj, Circle.coe_inv, mul_inv_cancel₀ v.coe_ne_zero]
  simp only [W, FlatScalar.firstIntegral_advance _ _ hu]

theorem W_transport (z : ℂ) (v : Circle) (i j : Fin 2) :
    Fourier.flatX (fun p w => W p w i j) z v = 0 := by
  have hb : DifferentiableAt ℝ (fun p => W p v i j) z := by
    have hc : DifferentiableAt ℝ (fun p : ℂ => conj p) z :=
      Complex.conjCLE.differentiable.differentiableAt
    fin_cases i <;> fin_cases j <;> simp [W, FlatScalar.firstIntegral]
    exact (differentiableAt_const _).mul hc
  have hd := TwistorDisk.line_derivative (fun p w => W p w i j) z v hb
  simp only [W_advance] at hd
  exact hd.unique (hasDerivAt_const 0 _)

/-- Smoothness of the first integral on the closed unit tangent bundle follows
from smoothness of the angle lift on the entire base plane. -/
theorem W_smooth (i j : Fin 2) :
    ContDiff ℝ ∞ (fun p : ℂ × ℝ => W p.1 (Circle.exp p.2) i j) := by
  have hangle : ContDiff ℝ ∞ (fun t : ℝ => (Circle.exp t : ℂ)) := by
    convert contDiff_circleMap 0 1 using 1
    funext t
    simp [circleMap, Circle.coe_exp]
  have hv : ContDiff ℝ ∞ (fun p : ℂ × ℝ => (Circle.exp p.2 : ℂ)) := hangle.comp contDiff_snd
  have hc : ContDiff ℝ ∞ (fun p : ℂ × ℝ => conj p.1) :=
    Complex.conjCLE.contDiff.comp contDiff_fst
  fin_cases i <;> fin_cases j
  · exact hv
  · exact contDiff_fst.sub ((hv.pow 2).mul hc)
  · exact contDiff_const
  · exact hv.inv (fun p => (Circle.exp p.2).coe_ne_zero)

/-- The exterior factor in the reciprocal velocity chart. -/
def exterior (z q : ℂ) : Mat := !![1, 0; q / z, 1]

def exteriorInv (z q : ℂ) : Mat := !![1, 0; -(q / z), 1]

/-- The interior factor and its adjugate. -/
def interior (z w : ℂ) : Mat :=
  !![w, FlatScalar.firstIntegral z w; -(1 / z), w * conj z / z]

def interiorInv (z w : ℂ) : Mat :=
  !![w * conj z / z, -FlatScalar.firstIntegral z w; 1 / z, w]

theorem exterior_normalized (z : ℂ) : exterior z 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [exterior]

theorem exterior_inverses (z q : ℂ) :
    exterior z q * exteriorInv z q = 1 ∧ exteriorInv z q * exterior z q = 1 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [exterior, exteriorInv, Matrix.mul_apply, Fin.sum_univ_two]

theorem interior_inverses {z : ℂ} (hz : z ≠ 0) (w : ℂ) :
    interior z w * interiorInv z w = 1 ∧ interiorInv z w * interior z w = 1 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [interior, interiorInv, FlatScalar.firstIntegral, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp [hz] <;> ring

theorem factorization {z w : ℂ} (hz : z ≠ 0) (hw : w ≠ 0) :
    W z w = exterior z w⁻¹ * interior z w := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [W, exterior, interior, FlatScalar.firstIntegral, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp [hz, hw] <;> ring

theorem interior_entire (z : ℂ) (i j : Fin 2) :
    Differentiable ℂ (fun w => interior z w i j) ∧
    Differentiable ℂ (fun w => interiorInv z w i j) := by
  constructor <;> fin_cases i <;> fin_cases j <;>
    simp [interior, interiorInv, FlatScalar.firstIntegral]

theorem exterior_entire (z : ℂ) (i j : Fin 2) :
    Differentiable ℂ (fun q => exterior z q i j) ∧
    Differentiable ℂ (fun q => exteriorInv z q i j) := by
  constructor <;> fin_cases i <;> fin_cases j <;> simp [exterior, exteriorInv]

local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

/-- The interior factors have vanishing negative Haar modes in `w`. -/
theorem interior_modes (z : ℂ) (i j : Fin 2) (k : ℤ) (hk : k < 0) :
    fourierCoeff (BoundaryModes.boundaryTrace (fun w => interior z w i j)) k = 0 ∧
    fourierCoeff (BoundaryModes.boundaryTrace (fun w => interiorInv z w i j)) k = 0 :=
  ⟨BoundaryModes.negativeMode_eq_zero (interior_entire z i j).1.diffContOnCl k hk,
   BoundaryModes.negativeMode_eq_zero (interior_entire z i j).2.diffContOnCl k hk⟩

/-- The exterior factors have vanishing negative Haar modes in the reciprocal chart. -/
theorem exterior_modes (z : ℂ) (i j : Fin 2) (k : ℤ) (hk : k < 0) :
    fourierCoeff (BoundaryModes.boundaryTrace (fun q => exterior z q i j)) k = 0 ∧
    fourierCoeff (BoundaryModes.boundaryTrace (fun q => exteriorInv z q i j)) k = 0 :=
  ⟨BoundaryModes.negativeMode_eq_zero (exterior_entire z i j).1.diffContOnCl k hk,
   BoundaryModes.negativeMode_eq_zero (exterior_entire z i j).2.diffContOnCl k hk⟩

end TransportOkaGrauert.JumpingLines
