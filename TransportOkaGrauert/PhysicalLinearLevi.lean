import TransportOkaGrauert.PhysicalLeviCalculus
import TransportOkaGrauert.PhysicalSteinDirections

/-! # Mixed Levi bounds for the two coordinate functions -/

noncomputable section
namespace TransportOkaGrauert.PhysicalLinearLevi

open Set Filter Metric Complex ChartStein CollarGluing FrameLevi PhysicalStein PhysicalSteinDirections
open scoped ContDiff Topology

private theorem derivative_vertical {σ : ℂ → ℝ} (hs : ContDiff ℝ ∞ σ) {p : E} (hp : ‖p.2‖ < 1)
    (u : E) (w : ℂ) : fderiv ℝ (J σ) p u (0,w) = 0 := by
  have d := ((J_smooth hs hp).differentiableAt (by simp)).hasFDerivAt.clm_apply (hasFDerivAt_const ((0,w):E) p)
  have eq : (fun y => J σ y (0,w)) =ᶠ[𝓝 p] (fun _ => ((0,I*w):E)) :=
    (continuous_snd.norm.continuousAt.eventually_lt_const hp).mono fun _ h => vertical_J σ h w
  have h := congrArg (fun L : E →L[ℝ] E => L u) (d.fderiv.symm.trans eq.fderiv_eq)
  simpa using h

private theorem derivative_bound {σ : ℂ → ℝ} (hs : ContDiff ℝ ∞ σ) {p : E} (hp : ‖p.2‖ < 1)
    (u v : E) : ‖fderiv ℝ (J σ) p u v‖ ≤ ‖fderiv ℝ (J σ) p‖ * ‖u‖ * ‖v.1‖ := by
  let D := fderiv ℝ (J σ) p
  have e : D u v = D u (v.1,0) := by
    calc D u v = D u ((v.1,0)+(0,v.2)) := by simp
      _ = _ := by rw [map_add,derivative_vertical hs hp,add_zero]
  rw [show fderiv ℝ (J σ) p u v = D u (v.1,0) from e]
  exact ((D u).le_opNorm _).trans (by simpa using mul_le_mul_of_nonneg_right (D.le_opNorm u) (norm_nonneg v.1))

private theorem horizontal_image {σ : ℂ → ℝ} {p : E} (hp : ‖p.2‖ < 1) (v : E) :
    ‖(J σ p v).1‖ ≤ ‖J σ p‖ * ‖v.1‖ := by
  rw [horizontal_part hp]
  exact (norm_fst_le _).trans (by simpa using (J σ p).le_opNorm ((v.1,0):E))

/-- The coordinate Levi forms vanish on a vertical complex line. Quantitatively
their absolute values are bounded by the product of the horizontal size and
the total size measured by the two complex-coordinate derivatives. -/
theorem coordinate_bounds {σ : ℂ → ℝ} (hs : ContDiff ℝ ∞ σ) {K : Set E} (hk : IsCompact K)
    (inside : K ⊆ domain) :
    ∃ M > 0, ∀ p ∈ K, ∀ v : E,
      let X := ‖pair (J σ p) x v‖
      let Y := ‖pair (J σ p) y v‖
      (v ≠ 0 → 0 < X+Y) ∧
      |ddC (J σ) x p v (J σ p v)| ≤ M*X*(X+Y) ∧
      |ddC (J σ) y p v (J σ p v)| ≤ M*X*(X+Y) := by
  obtain ⟨C,cp,bound⟩ := direction_bounds hs hk inside
  have jreg (p) (hp : p ∈ K) := J_smooth hs (inside hp).2
  have cc : ContinuousOn (fun p => ‖J σ p‖ + ‖fderiv ℝ (J σ) p‖) K := fun p hp =>
    ((jreg p hp).continuousAt.norm.add ((jreg p hp).fderiv_right (m := ∞) (by simp)).continuousAt.norm).continuousWithinAt
  obtain ⟨b,bb⟩ := hk.bddAbove_image cc
  let B := max 1 b
  have bp : 0 < B := zero_lt_one.trans_le (le_max_left ..)
  refine ⟨2*B*B*C*C,by positivity,?_⟩
  intro p hp v
  let X := ‖pair (J σ p) x v‖
  let Y := ‖pair (J σ p) y v‖
  have H := (bb (mem_image_of_mem _ hp)).trans (le_max_right 1 b)
  change ‖J σ p‖ + ‖fderiv ℝ (J σ) p‖ ≤ B at H
  have jb : ‖J σ p‖ ≤ B := by linarith [norm_nonneg (fderiv ℝ (J σ) p)]
  have db : ‖fderiv ℝ (J σ) p‖ ≤ B := by linarith [norm_nonneg (J σ p)]
  obtain ⟨h₁,h₂⟩ := bound p hp v
  have hJ : ‖J σ p v‖ ≤ B * ‖v‖ := ((J σ p).le_opNorm v).trans (mul_le_mul_of_nonneg_right jb (norm_nonneg _))
  have hJ₁ := (horizontal_image (inside hp).2 v).trans (mul_le_mul_of_nonneg_right jb (norm_nonneg _))
  have est (L : E →L[ℝ] ℝ) (hL : ∀ u, |L u| ≤ ‖u‖) :
      |ddC (J σ) L p v (J σ p v)| ≤ (2*B*B*C*C)*X*(X+Y) := by
    rw [PhysicalLeviCalculus.levi_linear L hs (inside hp).2]
    calc _ ≤ ‖fderiv ℝ (J σ) p (J σ p v) v‖ + ‖fderiv ℝ (J σ) p v (J σ p v)‖ :=
            (abs_sub _ _).trans (add_le_add (hL _) (hL _))
      _ ≤ ‖fderiv ℝ (J σ) p‖ * ‖J σ p v‖ * ‖v.1‖ + ‖fderiv ℝ (J σ) p‖ * ‖v‖ * ‖(J σ p v).1‖ :=
        add_le_add (derivative_bound hs (inside hp).2 _ _) (derivative_bound hs (inside hp).2 _ _)
      _ ≤ B*(B*‖v‖)*‖v.1‖ + B*‖v‖*(B*‖v.1‖) := by gcongr
      _ = (2*B*B)*‖v.1‖*‖v‖ := by ring
      _ ≤ (2*B*B)*(C*X)*(C*(X+Y)) := by gcongr
      _ = _ := by ring
  refine ⟨fun ne => pos_of_mul_pos_right ((norm_pos_iff.mpr ne).trans_le h₂) cp.le,
    est x (fun u => (abs_re_le_norm _).trans (norm_fst_le u)),
    est y (fun u => (abs_re_le_norm _).trans (norm_snd_le u))⟩

end TransportOkaGrauert.PhysicalLinearLevi
