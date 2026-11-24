import Mathlib.MeasureTheory.Measure.Haar.Unique
import TransportOkaGrauert.CoefficientBridge
import TransportOkaGrauert.ShiftedModes

/-! The canonical Birkhoff cell on one velocity circle. The disk functions
and their inverses are holomorphic in the interior and continuous up to
the circle. The obstruction therefore applies even at this regularity. -/
noncomputable section
namespace TransportOkaGrauert.BirkhoffCell
open Metric Complex Set
open scoped Matrix
abbrev Mat := Matrix (Fin 2) (Fin 2) ℂ
abbrev Loop := Circle → Mat
local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

structure Factor where
  val : ℂ → Mat
  inv : ℂ → Mat
  regular : ∀ i j, DiffContOnCl ℂ (fun w => val w i j) (ball 0 1)
  regularInv : ∀ i j, DiffContOnCl ℂ (fun w => inv w i j) (ball 0 1)
  inverses : ∀ w ∈ closedBall (0 : ℂ) 1, val w * inv w = 1 ∧ inv w * val w = 1

/-- A normalized exterior factor in the coordinate q=1/v, followed by
an interior factor in v. Both extend invertibly over their filled disks. -/
def BigCell (L : Loop) : Prop :=
  ∃ G F : Factor, G.val 0 = 1 ∧ ∀ v : Circle, L v = G.val (v : ℂ)⁻¹ * F.val v

/-- Matrix polynomials with polynomial inverses give disk factors. -/
def Factor.ofEntire (a b : ℂ → Mat)
    (h : ∀ i j, Differentiable ℂ (fun w => a w i j) ∧ Differentiable ℂ (fun w => b w i j))
    (hinv : ∀ w, a w * b w = 1 ∧ b w * a w = 1) : Factor :=
  ⟨a,b,fun i j => (h i j).1.diffContOnCl,fun i j => (h i j).2.diffContOnCl,fun w _ => hinv w⟩

def standard (c w : ℂ) : Mat := !![w,c; 0,w⁻¹]

private theorem circle_in_disk (v : Circle) : (v : ℂ) ∈ closedBall 0 1 := by
  simp [Metric.mem_closedBall]

private theorem reflected_coeff (g : ℂ → ℂ) (k : ℤ) :
    fourierCoeff (fun θ : DiskSeries.Angle => g (θ.toCircle : ℂ)⁻¹) k =
    fourierCoeff (BoundaryModes.boundaryTrace g) (-k) := by
  letI : MeasureTheory.Measure.Regular (AddCircle.haarAddCircle (T := 2 * Real.pi)) := by
    unfold AddCircle.haarAddCircle
    infer_instance
  unfold fourierCoeff
  rw [← MeasureTheory.integral_neg_eq_self _ AddCircle.haarAddCircle]
  simp only [fourier_apply, zsmul_neg', neg_neg, AddCircle.toCircle_neg,
    Circle.coe_inv, inv_inv, BoundaryModes.boundaryTrace]

/-- No exterior boundary value can equal v times an interior boundary
value unless both sides vanish. This uses actual normalized Haar modes. -/
theorem opposite_traces {f g : ℂ → ℂ}
    (hf : DiffContOnCl ℂ f (ball 0 1)) (hg : DiffContOnCl ℂ g (ball 0 1))
    (he : ∀ v : Circle, g (v : ℂ)⁻¹ = (v : ℂ) * f v) (v : Circle) : g (v : ℂ)⁻¹ = 0 := by
  let a (θ : DiskSeries.Angle) := g (θ.toCircle : ℂ)⁻¹
  have hcont : Continuous a := by
    apply hg.continuousOn.comp_continuous
    · change Continuous (fun θ : DiskSeries.Angle => (↑(θ.toCircle⁻¹) : ℂ))
      fun_prop
    · intro θ
      rw [closure_ball (0:ℂ) one_ne_zero]
      exact circle_in_disk θ.toCircle⁻¹
  have ha (k : ℤ) : fourierCoeff a k = 0 := by
    by_cases h : 0 < k
    · exact (reflected_coeff g k).trans (BoundaryModes.negativeMode_eq_zero hg _ (by omega))
    · have eqf : a = fun θ : DiskSeries.Angle => (θ.toCircle : ℂ) * f θ.toCircle :=
        funext fun θ => he θ.toCircle
      rw [eqf, ShiftedModes.coeff_shift]
      exact BoundaryModes.negativeMode_eq_zero hf _ (by omega)
  let θ : DiskSeries.Angle := (Complex.arg (v : ℂ) : ℝ)
  have hθ : θ.toCircle = v := (ChartModes.toCircle_angle _).trans (Circle.exp_arg v)
  simpa only [a, ContinuousMap.coe_mk, hθ] using
    CoefficientBridge.eq_zero_of_coeff_zero (⟨a,hcont⟩ : C(DiskSeries.Angle,ℂ)) ha θ

/-- The diagonal loop (v,v⁻¹) has no canonical factorization, even
without smoothness or an exterior normalization assumption. -/
theorem diagonal_obstruction (G F : Factor) :
    ¬ (∀ v : Circle, standard 0 v = G.val (v : ℂ)⁻¹ * F.val v) := by
  intro he
  have row (j : Fin 2) (v : Circle) : G.val (v : ℂ)⁻¹ 0 j = 0 := by
    apply opposite_traces (f := fun w => F.inv w 0 j) (g := fun q => G.val q 0 j)
      (F.regularInv 0 j) (G.regular 0 j) _ v
    intro w
    have h : standard 0 w * F.inv w = (G.val (w : ℂ)⁻¹ * F.val w) * F.inv w :=
      congrArg (· * F.inv w) (he w)
    rw [mul_assoc, (F.inverses w (circle_in_disk w)).1, mul_one] at h
    have hij := congrArg (fun M : Mat => M 0 j) h.symm
    simpa [standard, Matrix.mul_apply, Fin.sum_univ_two] using hij
  have hinv := (G.inverses (1:ℂ) (by simp [Metric.mem_closedBall])).1
  have h := congrArg (fun M : Mat => M 0 0) hinv
  have hr (j : Fin 2) : G.val 1 0 j = 0 := by simpa using row j 1
  simp [Matrix.mul_apply, hr] at h

theorem diagonal_not_big : ¬ BigCell (fun v => standard 0 v) := by
  rintro ⟨G,F,_,h⟩
  exact diagonal_obstruction G F h

private theorem regular_mul (A B : ℂ → Mat)
    (ha : ∀ i j, DiffContOnCl ℂ (fun w => A w i j) (ball 0 1))
    (hb : ∀ i j, DiffContOnCl ℂ (fun w => B w i j) (ball 0 1)) (i j) :
    DiffContOnCl ℂ (fun w => (A w * B w) i j) (ball 0 1) := by
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  exact ⟨((ha i 0).differentiableOn.mul (hb 0 j).differentiableOn).add
      ((ha i 1).differentiableOn.mul (hb 1 j).differentiableOn),
    ((ha i 0).continuousOn.mul (hb 0 j).continuousOn).add
      ((ha i 1).continuousOn.mul (hb 1 j).continuousOn)⟩

def Factor.times (F S : Factor) : Factor where
  val w := F.val w * S.val w
  inv w := S.inv w * F.inv w
  regular := regular_mul _ _ F.regular S.regular
  regularInv := regular_mul _ _ S.regularInv F.regularInv
  inverses w hw := by
    obtain ⟨a,b⟩ := F.inverses w hw
    obtain ⟨c,d⟩ := S.inverses w hw
    constructor
    · calc
        _ = F.val w * (S.val w * S.inv w) * F.inv w := by simp only [mul_assoc]
        _ = 1 := by rw [c, mul_one, a]
    · calc
        _ = S.inv w * (F.inv w * F.val w) * S.val w := by simp only [mul_assoc]
        _ = 1 := by rw [b, mul_one, d]

def Factor.swap (F : Factor) : Factor :=
  ⟨F.inv, F.val, F.regularInv, F.regular, fun w hw => (F.inverses w hw).symm⟩

private theorem bigCell_right (L : Loop) (S : Factor) (h : BigCell L) :
    BigCell (fun v => L v * S.val v) := by
  obtain ⟨G, F, hn, he⟩ := h
  refine ⟨G, F.times S, hn, ?_⟩
  intro v
  change L v * S.val v = _
  rw [he v, mul_assoc]
  rfl

theorem bigCell_right_iff (L : Loop) (S : Factor) :
    BigCell (fun v => L v * S.val v) ↔ BigCell L := by
  refine ⟨fun h => ?_, bigCell_right L S⟩
  have h' := bigCell_right _ S.swap h
  simpa only [Factor.swap, mul_assoc, (S.inverses _ (circle_in_disk _)).1, mul_one] using h'

/-- The scalar off-diagonal parameter is the exact test for the elementary
triangular loop with diagonal velocities v and v⁻¹. -/
theorem standard_big_iff (c : ℂ) : BigCell (fun v => standard c v) ↔ c ≠ 0 := by
  constructor
  · rintro h rfl
    exact diagonal_not_big h
  · intro hc
    let a (q : ℂ) : Mat := !![1,0; q/c, 1]
    let b (q : ℂ) : Mat := !![1,0; -(q/c), 1]
    let f (w : ℂ) : Mat := !![w,c; -(1/c),0]
    let g (w : ℂ) : Mat := !![0,-c; 1/c,w]
    have hext : ∀ i j, Differentiable ℂ (fun q => a q i j) ∧ Differentiable ℂ (fun q => b q i j) := by
      intro i j; constructor <;> fin_cases i <;> fin_cases j <;> simp [a,b]
    have hint : ∀ i j, Differentiable ℂ (fun w => f w i j) ∧ Differentiable ℂ (fun w => g w i j) := by
      intro i j; constructor <;> fin_cases i <;> fin_cases j <;> simp [f,g]
    have hextInv (q : ℂ) : a q * b q = 1 ∧ b q * a q = 1 := by
      constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp [a,b,Matrix.mul_apply,Fin.sum_univ_two]
    have hintInv (w : ℂ) : f w * g w = 1 ∧ g w * f w = 1 := by
      constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp [f,g,Matrix.mul_apply,Fin.sum_univ_two,hc] <;> ring
    refine ⟨Factor.ofEntire a b hext hextInv, Factor.ofEntire f g hint hintInv, ?_, ?_⟩
    · change a 0 = 1
      ext i j; fin_cases i <;> fin_cases j <;> simp [a]
    · intro v
      change standard c v = a (v : ℂ)⁻¹ * f v
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [a,f,standard,Matrix.mul_apply,Fin.sum_univ_two]
      all_goals field_simp [hc,v.coe_ne_zero]
      all_goals ring

end TransportOkaGrauert.BirkhoffCell
