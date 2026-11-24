import TransportOkaGrauert.SmoothTriangularLoop
import TransportOkaGrauert.PathContinuation

/-! Fiber algebra and transport differentiation for the closed-set
construction on curved surfaces. The scalar integrating factor and the
transport solution with prescribed mean are the geometric inputs. -/
noncomputable section
namespace TransportOkaGrauert.CurvedJump
open BirkhoffCell Metric PathContinuation Isothermal
open scoped ContDiff Matrix

def diagonalGauge (a b : ℂ) : Mat := !![a,0;0,b]

private theorem regular_diag (a b : ℂ → ℂ) (ha : DiffContOnCl ℂ a (ball 0 1))
    (hb : DiffContOnCl ℂ b (ball 0 1)) (i j : Fin 2) :
    DiffContOnCl ℂ (fun w => diagonalGauge (a w) (b w) i j) (ball 0 1) := by
  fin_cases i <;> fin_cases j
  all_goals first | exact ha | exact hb | exact (differentiable_const _).diffContOnCl

/-- The diagonal inside gauge for a scalar disk-holomorphic unit. -/
def gaugeFactor (q : ℂ → ℂ) (hq : DiffContOnCl ℂ q (ball 0 1))
    (hunit : ∀ w ∈ closedBall (0 : ℂ) 1, q w ≠ 0) : Factor where
  val w := diagonalGauge (q w) (q w)⁻¹
  inv w := diagonalGauge (q w)⁻¹ (q w)
  regular := by
    apply regular_diag _ _ hq
    exact ⟨hq.differentiableOn.inv (fun w hw => hunit w (ball_subset_closedBall hw)),
      hq.continuousOn.inv₀ (fun w hw => hunit w (by simpa [closure_ball, one_ne_zero] using hw))⟩
  regularInv := by
    apply regular_diag _ _ _ hq
    exact ⟨hq.differentiableOn.inv (fun w hw => hunit w (ball_subset_closedBall hw)),
      hq.continuousOn.inv₀ (fun w hw => hunit w (by simpa [closure_ball, one_ne_zero] using hw))⟩
  inverses w hw := by
    constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [diagonalGauge, Matrix.mul_apply, Fin.sum_univ_two, hunit w hw]

/-- The velocity, a scalar holomorphic integrating factor, and a second
solution of its transport equation give the matrix first integral. -/
def matrixValue (u q φ : ℂ) : Mat := !![u*q, φ/q; 0,(u*q)⁻¹]

theorem matrixValue_det {u q : ℂ} (φ : ℂ) (hu : u ≠ 0) (hq : q ≠ 0) :
    (matrixValue u q φ).det = 1 := by
  simp [matrixValue, Matrix.det_fin_two]
  field_simp [hu, hq]

private theorem value_as_gauge {q : ℂ → ℂ} (hq : DiffContOnCl ℂ q (ball 0 1))
    (hunit : ∀ w ∈ closedBall (0 : ℂ) 1, q w ≠ 0) (φ : Circle → ℂ) :
    (fun v : Circle => matrixValue v (q v) (φ v)) =
      fun v : Circle => standard (φ v) v * (gaugeFactor q hq hunit).val v := by
  funext v
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixValue, standard, gaugeFactor, diagonalGauge, Matrix.mul_apply,
      Fin.sum_univ_two, div_eq_mul_inv, mul_comm]

/-- A scalar holomorphic gauge converts the proposed velocity loop to the
triangular normal form. Its noncanonical fibers are exactly the zeros
of the actual angular mean of φ. -/
theorem cell_iff {q : ℂ → ℂ} (hq : DiffContOnCl ℂ q (ball 0 1))
    (hunit : ∀ w ∈ closedBall (0 : ℂ) 1, q w ≠ 0) (φ : Circle → ℂ)
    (hφ : ContDiff ℝ 2 (fun t : ℝ => φ (Circle.exp t))) :
    BigCell (fun v => matrixValue v (q v) (φ v)) ↔ TriangularLoop.coeff φ 0 ≠ 0 := by
  rw [value_as_gauge hq hunit φ, bigCell_right_iff, TriangularLoop.bigCell_iff φ hφ]

/-- The same criterion in the paper's smooth angular class, including
smoothness of the inverse traces. The mean is the prescribed datum in
Bohr–Paternain's two-mode lifting theorem. -/
theorem smooth_cell_iff {q : ℂ → ℂ} (hq : DiffContOnCl ℂ q (ball 0 1))
    (hunit : ∀ w ∈ closedBall (0 : ℂ) 1, q w ≠ 0)
    (hqθ : ContDiff ℝ ∞ (fun t : ℝ => q (Circle.exp t))) (φ : Circle → ℂ)
    (hφ : ContDiff ℝ ∞ (fun t : ℝ => φ (Circle.exp t))) :
    BoundaryJump.SmoothBigCell (fun v => matrixValue v (q v) (φ v)) ↔
      TriangularLoop.coeff φ 0 ≠ 0 := by
  have hi := hqθ.inv (fun t => hunit _ (by simp [Metric.mem_closedBall]))
  have hs : BoundaryJump.FactorSmooth (gaugeFactor q hq hunit) := by
    intro i j
    constructor <;> fin_cases i <;> fin_cases j
    all_goals first | exact hqθ | exact hi | exact contDiff_const
  rw [value_as_gauge hq hunit φ, SmoothCellChange.smoothBigCell_right_iff _ _ hs,
    SmoothTriangularLoop.smoothBigCell_iff φ hφ]

/-- Along a geodesic the unit angle has logarithmic derivative c.
The two matched scalar transport equations force every entry to be
constant to first order, including at segment endpoints. -/
theorem transport_on_curve (u q φ : ℝ → ℂ) {s : Set ℝ} {t : ℝ} {c : ℂ}
    (hu : HasDerivWithinAt u (c*u t) s t) (hq : HasDerivWithinAt q (-c*q t) s t)
    (hφ : HasDerivWithinAt φ (-c*φ t) s t) (hqu : q t ≠ 0) (huu : u t ≠ 0)
    (i j : Fin 2) : HasDerivWithinAt (fun x => matrixValue (u x) (q x) (φ x) i j) 0 s t := by
  have hb : HasDerivWithinAt (fun x => u x*q x) 0 s t := by
    convert hu.mul hq using 1
    ring
  have ha : HasDerivWithinAt (fun x => φ x/q x) 0 s t := by
    convert hφ.div hq hqu using 1
    ring
  fin_cases i <;> fin_cases j
  · exact hb
  · exact ha
  · exact hasDerivWithinAt_const t s 0
  · have hi := (hasDerivWithinAt_const t s (1 : ℂ)).div hb (by exact mul_ne_zero huu hqu)
    simp only [zero_mul, mul_zero, sub_zero, zero_div] at hi
    change HasDerivWithinAt (fun x => 1 / (u x * q x)) 0 s t at hi
    simpa only [one_div] using hi

end TransportOkaGrauert.CurvedJump
