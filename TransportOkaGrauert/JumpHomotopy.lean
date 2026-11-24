import TransportOkaGrauert.JumpingLines
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.Instances.Matrix

/-!
# A determinant-one null-homotopy of the Euclidean first integral

The boundary condition in Bohr–Paternain, Remark 2.4 and (5.8), concerns the
homotopy class of the full matrix map. We contract the map jointly in the base
point and unit direction by scaling the entries of five elementary shears.
-/

noncomputable section

namespace TransportOkaGrauert.JumpingLines

open scoped Matrix MatrixGroups ComplexConjugate
open unitInterval

private def upper (a : ℂ) : Mat := !![1, a; 0, 1]
private def lower (a : ℂ) : Mat := !![1, 0; a, 1]

@[fun_prop] private theorem upper_continuous : Continuous upper := by
  apply continuous_matrix
  intro i j
  fin_cases i <;> fin_cases j <;> simp [upper] <;> fun_prop

@[fun_prop] private theorem lower_continuous : Continuous lower := by
  apply continuous_matrix
  intro i j
  fin_cases i <;> fin_cases j <;> simp [lower] <;> fun_prop

private def shears (s w d h : ℂ) : Mat :=
  upper (s * (w - 1)) * lower s * upper (s * (d - 1)) *
    lower (-(s * w)) * upper (s * d * h)

private theorem shears_det (s w d h : ℂ) : (shears s w d h).det = 1 := by
  simp only [shears, Matrix.det_mul]
  simp [upper, lower, Matrix.det_fin_two]

private theorem shears_zero (w d h : ℂ) : shears 0 w d h = 1 := by
  have hu : upper 0 = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [upper]
  have hl : lower 0 = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [lower]
  simp [shears, hu, hl]

private theorem shears_one (w h : ℂ) (hw : w ≠ 0) :
    shears 1 w w⁻¹ h = !![w, h; 0, w⁻¹] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [shears, upper, lower, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp [hw] <;> ring_nf <;> simp

private theorem conj_eq_inv (v : Circle) : conj (v : ℂ) = (v : ℂ)⁻¹ := by
  rw [← Circle.coe_inv_eq_conj, Circle.coe_inv]

/-- The first integral as a continuous map on the whole plane times the direction circle. -/
def WMap : C(ℂ × Circle, SL(2, ℂ)) where
  toFun p := ⟨W p.1 p.2, W_det _ p.2.coe_ne_zero⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_matrix
    intro i j
    fin_cases i <;> fin_cases j <;> simp [W, FlatScalar.firstIntegral] <;>
      fun_prop (disch := exact fun p => p.2.coe_ne_zero)

/-- A joint null-homotopy in SL₂(ℂ). Restricting the base point gives the
same homotopy on the closed unit disk and its full boundary torus. -/
def WNullHomotopy : WMap.Homotopy (ContinuousMap.const _ (1 : SL(2, ℂ))) where
  toFun p :=
    let s := 1 - (p.1 : ℝ)
    let z := p.2.1
    let w := (p.2.2 : ℂ)
    ⟨shears s w (conj w) (FlatScalar.firstIntegral z w), shears_det ..⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    dsimp only
    unfold shears FlatScalar.firstIntegral
    fun_prop
  map_zero_left p := by
    apply Subtype.ext
    change shears (((1 : ℝ) - 0 : ℝ) : ℂ) (p.2 : ℂ) (conj (p.2 : ℂ)) _ = W p.1 p.2
    simpa [conj_eq_inv, W] using
      shears_one (p.2 : ℂ) (FlatScalar.firstIntegral p.1 p.2) p.2.coe_ne_zero
  map_one_left p := by
    apply Subtype.ext
    change shears (((1 : ℝ) - 1 : ℝ) : ℂ) _ _ _ = 1
    simp [shears_zero]

private def boundaryInclusion : C(Circle × Circle, ℂ × Circle) :=
  ⟨fun p => (p.1, p.2), by fun_prop⟩

private def intoGL : C(SL(2, ℂ), Matrix.GeneralLinearGroup (Fin 2) ℂ) :=
  ⟨Matrix.SpecialLinearGroup.toGL, Matrix.SpecialLinearGroup.continuous_toGL⟩

/-- The restriction of the first integral to the entire boundary torus, as a
general-linear-group-valued map. -/
def boundaryWMap : C(Circle × Circle, Matrix.GeneralLinearGroup (Fin 2) ℂ) :=
  intoGL.comp (WMap.comp boundaryInclusion)

theorem boundaryWMap_apply (p : Circle × Circle) :
    (boundaryWMap p : Mat) = W p.1 p.2 := rfl

/-- The full boundary map is homotopic to the identity matrix in GL₂(ℂ),
as required by the domain of the nonlinear Hilbert transform. -/
def boundaryWNullHomotopy : boundaryWMap.Homotopy (ContinuousMap.const _ 1) := by
  let H := (ContinuousMap.Homotopy.refl intoGL).comp
    (WNullHomotopy.compContinuousMap boundaryInclusion)
  apply H.cast rfl
  ext p : 1
  exact Matrix.SpecialLinearGroup.toGL.map_one

end TransportOkaGrauert.JumpingLines
