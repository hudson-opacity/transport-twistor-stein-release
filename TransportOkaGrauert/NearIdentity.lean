import TransportOkaGrauert.ChartModes
import TransportOkaGrauert.BoundaryModes
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Data.Matrix.Basis

/-! A boundary estimate for a fibrewise holomorphic matrix controls its norm
on the filled velocity disk. For a perturbation of the identity smaller
than one, Banach algebra inversion then supplies a holomorphic inverse and
preserves smoothness of the frame in the base and angular variables. -/

namespace TransportOkaGrauert.NearIdentity

open SimpleDiskTarget Metric Complex
open scoped Matrix.Norms.Operator ContDiff

noncomputable section
variable {n : ℕ}
local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

/-- The operator-norm maximum principle gives exactly the same radius on the
closed disk as on its boundary. -/
theorem norm_bound_on_disk {b : ℂ → Mat n} (hb : DiffContOnCl ℂ b (ball 0 1))
    {r : ℝ} (bound : ∀ v : Circle, ‖b v‖ ≤ r) {w : ℂ} (hw : w ∈ closedBall 0 1) :
    ‖b w‖ ≤ r := by
  apply norm_le_of_forall_mem_frontier_norm_le isBounded_ball hb
  · intro v hv
    rw [frontier_ball (0 : ℂ) one_ne_zero] at hv
    exact bound ⟨v, hv⟩
  · simpa only [closure_ball (0 : ℂ) one_ne_zero] using hw

private theorem isUnit_one_add {u : Mat n} (hu : ‖u‖ < 1) : IsUnit (1 + u) := by
  simpa only [sub_neg_eq_add] using isUnit_one_sub_of_norm_lt_one (x := -u) (by simpa using hu)

/-- The inverse is holomorphic on the disk interior and continuous to its
boundary, even when the prescribed strict bound is only on the circle. -/
theorem inverse_on_disk {b : ℂ → Mat n} (hb : DiffContOnCl ℂ b (ball 0 1))
    {r : ℝ} (hr : r < 1) (bound : ∀ v : Circle, ‖b v‖ ≤ r) :
    DiffContOnCl ℂ (fun w => Ring.inverse (1 + b w)) (ball 0 1) := by
  have unit (w : ℂ) (hw : w ∈ closedBall 0 1) :=
    isUnit_one_add ((norm_bound_on_disk hb bound hw).trans_lt hr)
  refine DiffContOnCl.mk_ball ?_ ?_
  · intro w hw
    have hd := differentiableAt_inverse (𝕜 := ℂ) (unit w (ball_subset_closedBall hw))
    exact hd.comp_differentiableWithinAt w ((hb.differentiableOn w hw).const_add 1)
  · intro w hw
    have hd := differentiableAt_inverse (𝕜 := ℂ) (unit w hw)
    exact hd.continuousAt.tendsto.comp ((hb.continuousOn_ball w hw).const_add 1)

private theorem smooth_matrix {F : Field n} (h : SmoothToBoundary F)
    (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) 1) (θ : ℝ) :
    ContDiffAt ℝ ∞ (fun p : ℂ × ℝ => F p.1 (Circle.exp p.2)) (z, θ) := by
  have hs : ContDiffAt ℝ ∞ (fun p : ℂ × ℝ =>
      ∑ i, ∑ j, F p.1 (Circle.exp p.2) i j • Matrix.single i j (1 : ℂ)) (z, θ) :=
    ContDiffAt.sum (fun i _ => ContDiffAt.sum (fun j _ => (h z hz θ i j).smul contDiffAt_const))
  simpa only [Matrix.smul_single, smul_eq_mul, mul_one, Matrix.sum_sum_single] using hs

private def ev (𝕜 : Type*) [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ℂ] (i j : Fin n) :
    Mat n →L[𝕜] ℂ := ⟨Matrix.entryLinearMap 𝕜 ℂ i j, (continuous_apply j).comp (continuous_apply i)⟩

private theorem scalar_entries {b : ℂ → Mat n} (h : DiffContOnCl ℂ b (ball 0 1)) (i j : Fin n) :
    DiffContOnCl ℂ (fun w => b w i j) (ball 0 1) :=
  ⟨(ev ℂ i j).differentiable.comp_differentiableOn h.differentiableOn,
    (ev ℂ i j).continuous.comp_continuousOn h.continuousOn⟩

private theorem matrix_regular {b : ℂ → Mat n}
    (h : ∀ i j, DiffContOnCl ℂ (fun w => b w i j) (ball 0 1)) :
    DiffContOnCl ℂ b (ball 0 1) := by
  have term i j := (h i j).smul_const (Matrix.single i j (1 : ℂ))
  have hd := DifferentiableOn.fun_sum (u := Finset.univ) fun i _ =>
    DifferentiableOn.fun_sum (u := Finset.univ) fun j _ => (term i j).differentiableOn
  have hc := continuousOn_finset_sum Finset.univ fun i _ =>
    continuousOn_finset_sum Finset.univ fun j _ => (term i j).continuousOn
  constructor
  · simpa only [Matrix.smul_single, smul_eq_mul, mul_one, Matrix.sum_sum_single] using hd
  · simpa only [Matrix.smul_single, smul_eq_mul, mul_one, Matrix.sum_sum_single] using hc

/-- A small matrix perturbation and its canonical inverse are both smooth
and fibrewise holomorphic; this assertion is independent of a transport PDE. -/
theorem gauge_of_small_extension (u : Field n)
    (smooth : SmoothToBoundary u)
    (extension : ∀ z ∈ closedBall (0 : ℂ) 1, ∃ b : ℂ → Mat n,
      (∀ i j, DiffContOnCl ℂ (fun w => b w i j) (ball 0 1)) ∧
      ∀ v : Circle, b v = u z v)
    {r : ℝ} (hr : r < 1) (bound : ∀ z ∈ closedBall (0 : ℂ) 1, ∀ v : Circle, ‖u z v‖ ≤ r) :
    let F : Field n := fun z v => 1 + u z v
    let G : Field n := fun z v => Ring.inverse (1 + u z v)
    SmoothToBoundary F ∧ SmoothToBoundary G ∧ ModesFrom 0 F ∧ ModesFrom 0 G ∧
      ∀ z ∈ closedBall (0 : ℂ) 1, ∀ v : Circle, F z v * G z v = 1 ∧ G z v * F z v = 1 := by
  dsimp only
  have unit z hz v := isUnit_one_add ((bound z hz v).trans_lt hr)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro z hz θ i j
    exact (ev ℝ i j).contDiff.contDiffAt.comp _ (contDiffAt_const.add (smooth_matrix smooth z hz θ))
  · intro z hz θ i j
    have inv : ContDiffAt ℝ ∞ Ring.inverse (1 + u z (Circle.exp θ)) :=
      contDiffAt_ringInverse ℝ (unit z hz (Circle.exp θ)).unit
    have hF : ContDiffAt ℝ ∞ (fun p : ℂ × ℝ => 1 + u p.1 (Circle.exp p.2)) (z, θ) :=
      contDiffAt_const.add (smooth_matrix smooth z hz θ)
    have hInv : ContDiffAt ℝ ∞ ((Ring.inverse : Mat n → Mat n) ∘
        (fun p : ℂ × ℝ => 1 + u p.1 (Circle.exp p.2))) (z, θ) :=
      ContDiffAt.comp (z, θ) (g := (Ring.inverse : Mat n → Mat n)) inv hF
    exact (ev ℝ i j).contDiff.contDiffAt.comp (z, θ) hInv
  · intro z hz i j k hk
    obtain ⟨b, hb, he⟩ := extension z hz
    have h := BoundaryModes.negativeMode_eq_zero
      (scalar_entries ((matrix_regular hb).const_add 1) i j) k hk
    change fourierCoeff (fun θ : AddCircle (2 * Real.pi) => (1 + b θ.toCircle) i j) k = 0 at h
    simpa only [he] using h
  · intro z hz i j k hk
    obtain ⟨b, hb, he⟩ := extension z hz
    have hi := inverse_on_disk (matrix_regular hb) hr (fun v => he v ▸ bound z hz v)
    have h := BoundaryModes.negativeMode_eq_zero (scalar_entries hi i j) k hk
    change fourierCoeff (fun θ : AddCircle (2 * Real.pi) => Ring.inverse (1 + b θ.toCircle) i j) k = 0 at h
    simpa only [he] using h
  · intro z hz v
    exact ⟨Ring.mul_inverse_cancel _ (unit z hz v), Ring.inverse_mul_cancel _ (unit z hz v)⟩

/-- A small smooth correction with nonnegative angular modes yields an
invertible holomorphic gauge. No differential equation is required. -/
theorem small_gauge (u : Field n) (smooth : SmoothToBoundary u) (modes : ModesFrom 0 u)
    {r : ℝ} (hr : r < 1) (bound : ∀ z ∈ closedBall (0 : ℂ) 1, ∀ v : Circle, ‖u z v‖ ≤ r) :
    ∃ G : Field n, SmoothToBoundary (fun z v => 1 + u z v) ∧ SmoothToBoundary G ∧
      ModesFrom 0 (fun z v => 1 + u z v) ∧ ModesFrom 0 G ∧
      ∀ z ∈ closedBall (0 : ℂ) 1, ∀ v : Circle,
        (1 + u z v) * G z v = 1 ∧ G z v * (1 + u z v) = 1 :=
  ⟨fun z v => Ring.inverse (1 + u z v),
    gauge_of_small_extension u smooth (ChartModes.matrix_extension u smooth modes) hr bound⟩

/-- When the near-identity gauge solves the chart transport equation, it
satisfies the chart's full frame predicate. -/
theorem frame_of_small_correction (lam : ℂ → ℝ) (A u : Field n)
    (smooth : SmoothToBoundary u) (modes : ModesFrom 0 u) {r : ℝ} (hr : r < 1)
    (bound : ∀ z ∈ closedBall (0 : ℂ) 1, ∀ v : Circle, ‖u z v‖ ≤ r)
    (transport : ∀ z ∈ closedBall (0 : ℂ) 1, ∀ (v : Circle) (i j : Fin n),
      Isothermal.geodesicX lam (fun p w => (1 + u p w) i j) z v + (A z v * (1 + u z v)) i j = 0) :
    IsFrame lam A (fun z v => 1 + u z v) (fun z v => Ring.inverse (1 + u z v)) := by
  obtain ⟨hf, hg, mf, mg, hfg⟩ :=
    gauge_of_small_extension u smooth (ChartModes.matrix_extension u smooth modes) hr bound
  exact ⟨hf, hg, mf, mg, hfg, transport⟩

end
end TransportOkaGrauert.NearIdentity
