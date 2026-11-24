import TransportOkaGrauert.ExteriorChange
import TransportOkaGrauert.BoundaryJump

/-! Changes of smooth disk factors in a normalized Birkhoff factorization. -/

noncomputable section
namespace TransportOkaGrauert.SmoothCellChange

open BirkhoffCell BoundaryJump Metric
open scoped ContDiff ComplexConjugate Matrix

private theorem smooth_entries_mul {a b : ℂ → Mat}
    (ha : ∀ i j, ContDiff ℝ ∞ (fun t : ℝ => a (Circle.exp t) i j))
    (hb : ∀ i j, ContDiff ℝ ∞ (fun t : ℝ => b (Circle.exp t) i j)) (i j) :
    ContDiff ℝ ∞ (fun t : ℝ => (a (Circle.exp t) * b (Circle.exp t)) i j) := by
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  exact ((ha i 0).mul (hb 0 j)).add ((ha i 1).mul (hb 1 j))

theorem times_smooth {A B : Factor} (ha : FactorSmooth A) (hb : FactorSmooth B) :
    FactorSmooth (A.times B) := fun i j =>
  ⟨smooth_entries_mul (fun i j => (ha i j).1) (fun i j => (hb i j).1) i j,
   smooth_entries_mul (fun i j => (hb i j).2) (fun i j => (ha i j).2) i j⟩

theorem swap_smooth {A : Factor} (ha : FactorSmooth A) : FactorSmooth A.swap :=
  fun i j => (ha i j).symm

theorem center_smooth (A : Factor) : FactorSmooth A.center :=
  fun _ _ => ⟨contDiff_const, contDiff_const⟩

theorem normalizeExterior_smooth {A : Factor} (ha : FactorSmooth A) :
    FactorSmooth A.normalizeExterior := times_smooth ha (swap_smooth (center_smooth A))

theorem upperFactor_smooth {p : ℂ → ℂ} (hp : DiffContOnCl ℂ p (ball 0 1))
    (hs : ContDiff ℝ ∞ (fun t : ℝ => p (Circle.exp t))) : FactorSmooth (upperFactor p hp) := by
  intro i j
  constructor <;> fin_cases i <;> fin_cases j <;> simp [upperFactor, upperShear]
  all_goals first | exact hs | exact hs.neg | exact contDiff_const

/-- The zero upper shear is the identity factor in either disk chart. -/
def identityFactor : Factor := upperFactor (fun _ : ℂ => 0) (differentiable_const _).diffContOnCl

@[simp] theorem identityFactor_val (w : ℂ) : identityFactor.val w = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [identityFactor, upperFactor, upperShear]

theorem identityFactor_smooth : FactorSmooth identityFactor := upperFactor_smooth _ contDiff_const

theorem smoothBigCell_of_unnormalized (L : Loop) (X F : Factor)
    (hx : FactorSmooth X) (hf : FactorSmooth F)
    (h : ∀ v : Circle, L v = X.val (v : ℂ)⁻¹ * F.val v) : SmoothBigCell L := by
  refine ⟨X.normalizeExterior, X.center.times F, normalizeExterior_smooth hx,
    times_smooth (center_smooth X) hf, X.normalizeExterior_zero, ?_⟩
  intro v
  change L v = (X.val (v : ℂ)⁻¹ * X.inv 0) * (X.val 0 * F.val v)
  rw [h, mul_assoc, ← mul_assoc (X.inv 0), (X.inverses 0 (by simp)).2, one_mul]

private theorem smoothBigCell_left (L : Loop) (S : Factor) (hs : FactorSmooth S)
    (hL : SmoothBigCell L) : SmoothBigCell (fun v => S.val (v : ℂ)⁻¹ * L v) := by
  obtain ⟨G, F, hg, hf, _, h⟩ := hL
  apply smoothBigCell_of_unnormalized _ (S.times G) F (times_smooth hs hg) hf
  intro v
  change S.val (v : ℂ)⁻¹ * L v = (S.val (v : ℂ)⁻¹ * G.val (v : ℂ)⁻¹) * F.val v
  rw [h, mul_assoc]

theorem smoothBigCell_left_iff (L : Loop) (S : Factor) (hs : FactorSmooth S) :
    SmoothBigCell (fun v => S.val (v : ℂ)⁻¹ * L v) ↔ SmoothBigCell L := by
  refine ⟨fun h => ?_, smoothBigCell_left L S hs⟩
  have h' := smoothBigCell_left _ S.swap (swap_smooth hs) h
  have hcancel (v : Circle) : S.inv (v : ℂ)⁻¹ * S.val (v : ℂ)⁻¹ = 1 :=
    (S.inverses _ (by simp [mem_closedBall])).2
  simpa only [Factor.swap, ← mul_assoc, hcancel, one_mul] using h'

private theorem smoothBigCell_right (L : Loop) (S : Factor) (hs : FactorSmooth S)
    (hL : SmoothBigCell L) : SmoothBigCell (fun v => L v * S.val v) := by
  obtain ⟨G, F, hg, hf, hn, h⟩ := hL
  refine ⟨G, F.times S, hg, times_smooth hf hs, hn, ?_⟩
  intro v
  change L v * S.val v = G.val (v : ℂ)⁻¹ * (F.val v * S.val v)
  rw [h, mul_assoc]

theorem smoothBigCell_right_iff (L : Loop) (S : Factor) (hs : FactorSmooth S) :
    SmoothBigCell (fun v => L v * S.val v) ↔ SmoothBigCell L := by
  refine ⟨fun h => ?_, smoothBigCell_right L S hs⟩
  have h' := smoothBigCell_right _ S.swap (swap_smooth hs) h
  have hcancel (v : Circle) : S.val v * S.inv v = 1 :=
    (S.inverses _ (by simp [mem_closedBall])).1
  simpa only [Factor.swap, mul_assoc, hcancel, mul_one] using h'

/-- The elementary triangular loop is canonically factorizable by smooth
factors exactly when its constant off-diagonal coefficient is nonzero. -/
theorem standard_smooth_iff (c : ℂ) : SmoothBigCell (fun v => standard c v) ↔ c ≠ 0 := by
  refine ⟨fun h => (standard_big_iff c).mp h.bigCell, fun hc => ?_⟩
  let p : ℂ → ℂ := fun w => w * conj c
  have hp : DiffContOnCl ℂ p (ball 0 1) := (differentiable_id.mul_const (conj c)).diffContOnCl
  let S := upperFactor p hp
  have hv : ContDiff ℝ ∞ (fun t : ℝ => (Circle.exp t : ℂ)) := by
    simp only [Circle.coe_exp]
    exact (Complex.ofRealCLM.contDiff.mul contDiff_const).cexp
  have hs : FactorSmooth S := upperFactor_smooth hp (hv.mul contDiff_const)
  have he : (fun v : Circle => standard c v) =
      fun v : Circle => JumpingLines.W c v * S.val v := by
    funext v
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [S, p, standard, JumpingLines.W, FlatScalar.firstIntegral, upperFactor, upperShear,
        Matrix.mul_apply, Fin.sum_univ_two]
    ring
  rw [he]
  exact smoothBigCell_right _ S hs (smooth_at_regular_fiber hc)

end TransportOkaGrauert.SmoothCellChange
