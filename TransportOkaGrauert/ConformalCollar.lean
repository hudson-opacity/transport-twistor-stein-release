import TransportOkaGrauert.SimpleDiskTarget
import TransportOkaGrauert.LeviBoundary
import TransportOkaGrauert.ConformalFrame
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# A strictly concave defining function for a conformal disk

For the metric `exp(2σ)(dx²+dy²)`, correct the Euclidean disk defining
function by subtracting a large multiple of its square. Strict convexity
controls the tangent direction. Completing the square absorbs the radial
mixed term, uniformly over the boundary. The Hessian is calculated from
real Fréchet derivatives in the isothermal coordinates.
-/

noncomputable section
namespace TransportOkaGrauert.ConformalCollar

open Complex SimpleDiskTarget Set Metric
open scoped ContDiff Topology

/-- Euclidean scalar product in the fixed chart. -/
def dot (z v : ℂ) : ℝ := z.re * v.re + z.im * v.im

/-- Positive in the open unit disk. -/
def b₀ (z : ℂ) : ℝ := 1 - Complex.normSq z

def defining (L : ℝ) (z : ℂ) : ℝ := b₀ z - L * (b₀ z) ^ 2

/-- Coordinate formula for the covariant Hessian of `f` in a vector `v`.
The connection of the conformal metric contributes the last two terms. -/
def conformalHessian (σ f : ℂ → ℝ) (z v : ℂ) : ℝ :=
  fderiv ℝ (fun y => fderiv ℝ f y v) z v -
    2 * fderiv ℝ σ z v * fderiv ℝ f z v +
    ‖v‖ ^ 2 * (fderiv ℝ σ z 1 * fderiv ℝ f z 1 + fderiv ℝ σ z I * fderiv ℝ f z I)

/-- Evaluates the Hessian on the metric-unit vector represented by a Euclidean
unit direction `v`; the factor accounts for both vector arguments. -/
def unitHessian (σ f : ℂ → ℝ) (z v : ℂ) : ℝ :=
  Real.exp (-2 * σ z) * conformalHessian σ f z v

private theorem b₀_eq (z : ℂ) : b₀ z = 1 - (z.re ^ 2 + z.im ^ 2) := by
  simp [b₀, Complex.normSq_apply, pow_two]

private theorem hasFDerivAt_b₀ (z : ℂ) :
    HasFDerivAt b₀ (0 - ((2 * z.re) • reCLM + (2 * z.im) • imCLM)) z := by
  have h := (hasFDerivAt_const (𝕜 := ℝ) (1 : ℝ) z).sub
    ((reCLM.hasFDerivAt.pow 2).add (imCLM.hasFDerivAt.pow 2))
  simpa [funext b₀_eq, two_smul, two_mul] using h

private theorem fderiv_defining (L : ℝ) (z v : ℂ) :
    fderiv ℝ (defining L) z v = -2 * (1 - 2 * L * b₀ z) * dot z v := by
  have h₀ := hasFDerivAt_b₀ z
  have h := h₀.sub ((h₀.pow 2).const_mul L)
  change HasFDerivAt (defining L) _ z at h
  rw [h.fderiv]
  simp [dot]
  ring

private theorem second_defining (L : ℝ) (z v : ℂ) :
    fderiv ℝ (fun y => fderiv ℝ (defining L) y v) z v =
      -2 * (1 - 2 * L * b₀ z) * ‖v‖ ^ 2 - 8 * L * dot z v ^ 2 := by
  have hp := (reCLM.hasFDerivAt (x := z)).mul_const v.re
  have hq := (imCLM.hasFDerivAt (x := z)).mul_const v.im
  have h := (((hasFDerivAt_const (𝕜 := ℝ) (1 : ℝ) z).sub
    ((hasFDerivAt_b₀ z).const_mul (2 * L))).const_mul (-2)).mul (hp.add hq)
  simp_rw [fderiv_defining]
  change HasFDerivAt (fun y => -2 * (1 - 2 * L * b₀ y) * dot y v) _ z at h
  rw [h.fderiv]
  rw [← Complex.normSq_eq_norm_sq]
  simp [dot, Complex.normSq_apply]
  ring

private theorem in_coordinates (D : ℂ →L[ℝ] ℝ) (v : ℂ) :
    D v = v.re * D 1 + v.im * D I := by
  have heq : v.re • (1 : ℂ) + v.im • I = v := by simp [Complex.real_smul, Complex.re_add_im]
  calc
    _ = D (v.re • (1 : ℂ) + v.im • I) := congrArg _ heq.symm
    _ = _ := by rw [map_add, map_smul, map_smul]; rfl

/-- The coordinate Hessian is the actual second derivative on a geodesic
with the Christoffel equations from the isothermal chart. -/
theorem derivative_along_geodesic {σ f : ℂ → ℝ} {γ V : ℝ → ℂ} {t : ℝ} {a : ℂ}
    (hf : ContDiffAt ℝ 2 f (γ t)) (hγ : HasDerivAt γ (V t) t) (hV : HasDerivAt V a t)
    (geo : Isothermal.geodesicEquations (fderiv ℝ σ (γ t) 1) (fderiv ℝ σ (γ t) I)
      (V t).re (V t).im a.re a.im) :
    HasDerivAt (fun s => fderiv ℝ f (γ s) (V s)) (conformalHessian σ f (γ t) (V t)) t := by
  have hdf := ((hf.fderiv_right (m := 1) (by decide)).differentiableAt one_ne_zero).hasFDerivAt
  have chain := (hdf.comp_hasDerivAt t hγ).clm_apply hV
  have fixed := hdf.clm_apply (hasFDerivAt_const (𝕜 := ℝ) (V t) (γ t))
  have eq : fderiv ℝ (fun y => fderiv ℝ f y (V t)) (γ t) (V t) =
      fderiv ℝ (fderiv ℝ f) (γ t) (V t) (V t) := by
    rw [fixed.fderiv]
    simp
  convert chain using 1
  simp only [Function.comp_apply]
  rw [conformalHessian, eq, in_coordinates (fderiv ℝ σ (γ t)) (V t),
    in_coordinates (fderiv ℝ f (γ t)) (V t), in_coordinates (fderiv ℝ f (γ t)) a,
    ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  obtain ⟨ex, ey⟩ := geo
  linear_combination -(fderiv ℝ f (γ t) 1) * ex - (fderiv ℝ f (γ t) I) * ey

/-- The full conformal Hessian, including its off-diagonal radial term. -/
theorem conformalHessian_defining (σ : ℂ → ℝ) (L : ℝ) (z v : ℂ) :
    conformalHessian σ (defining L) z v =
      (1 - 2 * L * b₀ z) * (-2 * ‖v‖ ^ 2 * (1 + fderiv ℝ σ z z) +
        4 * fderiv ℝ σ z v * dot z v) - 8 * L * dot z v ^ 2 := by
  rw [conformalHessian, second_defining]
  simp only [fderiv_defining, in_coordinates (fderiv ℝ σ z) z]
  simp [dot]
  ring

private def upper (σ : ℂ → ℝ) (L : ℝ) (z : ℂ) : ℝ :=
  let k := 1 - 2 * L * b₀ z
  Real.exp (-2 * σ z) *
    (-2 * k * (1 + fderiv ℝ σ z z) + (k * ‖fderiv ℝ σ z‖) ^ 2 / (2 * L))

private theorem unitHessian_le_upper (σ : ℂ → ℝ) {L : ℝ} (hL : 0 < L)
    (z v : ℂ) (hv : ‖v‖ = 1) : unitHessian σ (defining L) z v ≤ upper σ L z := by
  unfold unitHessian upper
  rw [conformalHessian_defining, hv]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  let k := 1 - 2 * L * b₀ z
  let D := fderiv ℝ σ z
  let s := dot z v
  change k * (-2 * 1 ^ 2 * (1 + D z) + 4 * D v * s) - 8 * L * s ^ 2 ≤
    -2 * k * (1 + D z) + (k * ‖D‖) ^ 2 / (2 * L)
  have hv' : |D v| ≤ ‖D‖ := by simpa [Real.norm_eq_abs, hv] using D.le_opNorm v
  have hsq : (D v) ^ 2 ≤ ‖D‖ ^ 2 := sq_le_sq.mpr (by simpa using hv')
  have hk := mul_le_mul_of_nonneg_left hsq (sq_nonneg k)
  have hcross : 4 * k * D v * s - 8 * L * s ^ 2 ≤ (k * ‖D‖) ^ 2 / (2 * L) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * L)).mpr
    nlinarith [sq_nonneg (4 * L * s - k * D v)]
  linarith only [hcross]

private theorem continuous_curvature {σ : ℂ → ℝ} (hσ : ContDiff ℝ ∞ σ) :
    Continuous (curvature σ) := by
  have hd := hσ.fderiv_right (m := ∞) (by simp)
  have h₁ := (hd.clm_apply (contDiff_const (c := (1 : ℂ)))).fderiv_right (m := ∞) (by simp)
  have hI := (hd.clm_apply (contDiff_const (c := I))).fderiv_right (m := ∞) (by simp)
  exact ((continuous_const.mul hσ.continuous).rexp.neg).mul
    ((h₁.continuous.clm_apply continuous_const).add (hI.continuous.clm_apply continuous_const))

private theorem b₀_boundary {z : ℂ} (hz : z ∈ sphere (0 : ℂ) 1) : b₀ z = 0 := by
  have hz' : ‖z‖ = 1 := by simpa [mem_sphere] using hz
  simp [b₀, Complex.normSq_eq_norm_sq, hz']

/-- Uniform negative Hessian on a neighborhood of the entire circle, in
all metric-unit directions. Inside the disk the defining function is positive,
and curvature times its size is smaller than the Hessian margin. -/
theorem exists_strict_collar {σ : ℂ → ℝ} (simple : SimpleMetric σ) :
    ∃ L > 0, ∃ η > 0, ∃ N : Set ℂ, IsOpen N ∧ sphere (0 : ℂ) 1 ⊆ N ∧
      (∀ z ∈ N, ∀ v : ℂ, ‖v‖ = 1 → unitHessian σ (defining L) z v ≤ -η) ∧
      ∀ z ∈ N, ‖z‖ < 1 → 0 < defining L z ∧ defining L z * |curvature σ z| < η := by
  let A := fun z : ℂ => 1 + fderiv ℝ σ z z
  have hD := (simple.smooth.fderiv_right (m := ∞) (by simp)).continuous
  have hA : Continuous A := continuous_const.add (hD.clm_apply continuous_id)
  have hpos : ∀ z ∈ sphere (0 : ℂ) 1, 0 < A z := simple.strictConvex
  have hs := isCompact_sphere (0 : ℂ) 1
  have hne : (sphere (0 : ℂ) 1).Nonempty := ⟨1, by simp⟩
  let ratio := fun z : ℂ => ‖fderiv ℝ σ z‖ ^ 2 / (2 * A z)
  have hratio : ContinuousOn ratio (sphere (0 : ℂ) 1) :=
    (hD.norm.pow 2).continuousOn.div (continuous_const.mul hA).continuousOn
      (fun z hz => ne_of_gt (mul_pos (by norm_num) (hpos z hz)))
  obtain ⟨zm, _, hmax⟩ := hs.exists_isMaxOn hne hratio
  let L := max 1 (ratio zm)
  have hL : 0 < L := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hb₀ : Continuous b₀ := continuous_const.sub Complex.continuous_normSq
  have hb : Continuous (defining L) := hb₀.sub (continuous_const.mul (hb₀.pow 2))
  have hk : Continuous (fun z => 1 - 2 * L * b₀ z) := continuous_const.sub (continuous_const.mul hb₀)
  have hu : Continuous (upper σ L) :=
    (continuous_const.mul simple.smooth.continuous).rexp.mul
      (((continuous_const.mul hk).mul hA).add (((hk.mul hD.norm).pow 2).div_const _))
  have hnegative (z : ℂ) (hz : z ∈ sphere (0 : ℂ) 1) : upper σ L z < 0 := by
    have hr : ratio z ≤ L := (isMaxOn_iff.mp hmax z hz).trans (le_max_right _ _)
    have hbound : ‖fderiv ℝ σ z‖ ^ 2 / (2 * L) ≤ A z := by
      apply (div_le_iff₀ (mul_pos (by norm_num) hL)).mpr
      have h := (div_le_iff₀ (mul_pos (by norm_num) (hpos z hz))).mp hr
      linarith
    simp only [upper, b₀_boundary hz, mul_zero, sub_zero, mul_one, one_mul]
    exact mul_neg_of_pos_of_neg (Real.exp_pos _) (by dsimp [A] at hbound; linarith [hpos z hz])
  obtain ⟨zm', hzm', hmax'⟩ := hs.exists_isMaxOn hne hu.continuousOn
  let η := -upper σ L zm' / 2
  have hη : 0 < η := by dsimp [η]; linarith [hnegative zm' hzm']
  let N := {z : ℂ | upper σ L z < -η} ∩ {z : ℂ | 0 < 1 - L * b₀ z} ∩
    {z : ℂ | defining L z * |curvature σ z| < η}
  have hopen : IsOpen N := ((isOpen_lt hu continuous_const).inter
    (isOpen_lt continuous_const (continuous_const.sub (continuous_const.mul hb₀)))).inter
    (isOpen_lt (hb.mul (continuous_curvature simple.smooth).abs) continuous_const)
  refine ⟨L, hL, η, hη, N, hopen, ?_, ?_, ?_⟩
  · intro z hz
    refine ⟨⟨?_, by simp [b₀_boundary hz]⟩, by simpa [defining, b₀_boundary hz] using hη⟩
    change upper σ L z < -η
    dsimp [η]
    linarith [isMaxOn_iff.mp hmax' z hz, hnegative zm' hzm']
  · intro z hz v hv
    exact (unitHessian_le_upper σ hL z v hv).trans hz.1.1.le
  · intro z hz hinside
    have hbpos : 0 < b₀ z := by
      rw [b₀, Complex.normSq_eq_norm_sq]
      nlinarith [norm_nonneg z]
    refine ⟨?_, hz.2⟩
    rw [show defining L z = b₀ z * (1 - L * b₀ z) by unfold defining; ring]
    exact mul_pos hbpos hz.1.2

/-- First derivative on the metric-unit vector with Euclidean direction `v`. -/
def unitSlope (σ f : ℂ → ℝ) (z v : ℂ) : ℝ :=
  Real.exp (-σ z) * fderiv ℝ f z v

/-- Insert the derivatives of the explicit base defining function in the
Levi matrix. The horizontal directions are the metric-unit lifts of `v`
and its rotation `I * v`. -/
def sideJet (σ : ℂ → ℝ) (L : ℝ) (z v : ℂ) : LeviBoundary.FrameJet :=
  let b := defining L
  LeviBoundary.baseJet (curvature σ z) (b z)
    (unitSlope σ b z v) (unitSlope σ b z (I * v))
    (unitHessian σ b z v) (unitHessian σ b z (I * v))

/-- At every point of a single base collar, the vertical entry and the Schur
complement are strictly positive for the entire punctured open velocity
disk (`0 < t < 1`), including arbitrarily close to the corner. -/
theorem exists_positive_side {σ : ℂ → ℝ} (simple : SimpleMetric σ) :
    ∃ L > 0, ∃ N : Set ℂ, IsOpen N ∧ sphere (0 : ℂ) 1 ⊆ N ∧
      ∀ z ∈ N, ‖z‖ < 1 → 0 < defining L z ∧
        ∀ v : ℂ, ‖v‖ = 1 → ∀ t : ℝ, 0 < t → t < 1 →
          0 < LeviBoundary.vertical t (sideJet σ L z v) ∧
          0 < LeviBoundary.schur t (sideJet σ L z v) := by
  obtain ⟨L, hL, η, hη, N, hopen, hcircle, hess, inside⟩ := exists_strict_collar simple
  refine ⟨L, hL, N, hopen, hcircle, ?_⟩
  intro z hz hz'
  obtain ⟨hb, hK⟩ := inside z hz hz'
  refine ⟨hb, ?_⟩
  intro v hv t ht ht'
  have hden : 0 < 1 - t ^ 2 := by nlinarith
  constructor
  · simpa [sideJet, LeviBoundary.vertical, LeviBoundary.baseJet] using
      div_pos hden (sq_pos_of_pos ht)
  · let K := curvature σ z
    let b := defining L z
    let xx := unitHessian σ (defining L) z v
    let hh := unitHessian σ (defining L) z (I * v)
    have hxx : xx ≤ -η := hess z hz v hv
    have hhh : hh ≤ -η := hess z hz _ (by simp [hv])
    have lower : η / b ≤ -(xx + t ^ 2 * hh) / b := by
      apply div_le_div_of_nonneg_right _ hb.le
      linarith [mul_nonpos_of_nonneg_of_nonpos (sq_nonneg t) (show hh ≤ 0 by linarith)]
    have hcurv : (1 - t) * K ≤ |K| :=
      calc
        _ ≤ (1 - t) * |K| := mul_le_mul_of_nonneg_left (le_abs_self _) (by linarith)
        _ ≤ 1 * |K| := mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
        _ = _ := one_mul _
    have hdom : |K| < η / b := (lt_div_iff₀ hb).mpr (by simpa [mul_comm, K, b] using hK)
    rw [sideJet, LeviBoundary.base_schur ht.ne' hden.ne' hb.ne']
    change 0 < -(xx + t ^ 2 * hh) / b - (1 - t) * K +
      t ^ 2 * (unitSlope σ (defining L) z v / b) ^ 2 +
      t ^ 4 * (unitSlope σ (defining L) z (I * v) / b) ^ 2
    exact add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg
      (sub_pos.mpr (hcurv.trans_lt (hdom.trans_le lower))) (by positivity)) (by positivity)

/-- The equation defining the radial parameter in the punctured fibre. -/
def radialParameter (r : ℝ) : ℝ := (1-r^2)/(1+r^2)

/-- Entries on the frame with its two vertical vectors divided by `r`.
These expressions also make sense on the zero section. -/
def normalizedSide (j : LeviBoundary.FrameJet) (r : ℝ) : ℝ × ℝ × ℝ × ℝ :=
  (LeviBoundary.horizontal (radialParameter r) j, 4 / (1-r^2)^2,
    4*r/(1-r^4) * j.x, -4*r/(1+r^2)^2 * j.h)

/-- On the punctured disk the continuous expressions are exactly the Levi
entries on the normalized frame, including the apparently singular mixed term. -/
theorem normalizedSide_eq {r : ℝ} (hr : 0 < r) (hr' : r < 1)
    (K b bx bh bxx bhh : ℝ) :
    let j := LeviBoundary.baseJet K b bx bh bxx bhh
    let t := radialParameter r
    normalizedSide j r = (LeviBoundary.horizontal t j, LeviBoundary.vertical t j / r^2,
      LeviBoundary.mixedJ t j / r, LeviBoundary.mixedR t j / r) := by
  have h1 : 0 < 1 - r^2 := by nlinarith
  have h2 : 0 < 1 + r^2 := by positivity
  have h4 : 0 < 1 - r^4 := by nlinarith [mul_pos h1 h2]
  dsimp [normalizedSide, LeviBoundary.vertical, LeviBoundary.mixedJ, LeviBoundary.mixedR,
    LeviBoundary.baseJet, radialParameter]
  refine Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ ?_)) <;>
    field_simp [hr.ne', h1.ne', h2.ne', h4.ne'] <;> ring

theorem normalizedSide_continuousAt_zero (j : LeviBoundary.FrameJet) :
    ContinuousAt (normalizedSide j) 0 := by
  unfold normalizedSide LeviBoundary.horizontal radialParameter
  fun_prop (disch := norm_num)

/-- The actual limiting matrix is diagonal. Its vertical entry is four;
on the base collar the horizontal entry is strictly positive. -/
theorem normalizedSide_zero_positive {σ : ℂ → ℝ} {L : ℝ} {z v : ℂ}
    (hb : 0 < defining L z) (hx : unitHessian σ (defining L) z v < 0)
    (hh : unitHessian σ (defining L) z (I * v) < 0) :
    ∃ A > 0, normalizedSide (sideJet σ L z v) 0 = (A, 4, 0, 0) := by
  let j := sideJet σ L z v
  refine ⟨j.xx + j.hh, ?_, ?_⟩
  · dsimp [j, sideJet, LeviBoundary.baseJet]
    have h₁ := div_neg_of_neg_of_pos hx hb
    have h₂ := div_neg_of_neg_of_pos hh hb
    simp only [neg_div]
    linarith [sq_nonneg (unitSlope σ (defining L) z v / defining L z),
      sq_nonneg (unitSlope σ (defining L) z (I * v) / defining L z)]
  · simp [normalizedSide, radialParameter, LeviBoundary.horizontal, j]

section Polar

open ConformalFrame FrameLevi Filter

private def baseCLM : Chart →L[ℝ] ℂ := .fst ℝ ℂ (ℝ × ℝ)
private def angleCLM : Chart →L[ℝ] ℝ := (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (.snd ℝ ℂ (ℝ × ℝ))

private theorem norm_unit (θ : ℝ) : ‖unit θ‖ = 1 := by
  have h : Complex.normSq (unit θ) = 1 := by
    simp [Complex.normSq_apply, unit, Complex.real_smul, -Complex.ofReal_cos, -Complex.ofReal_sin]
    nlinarith [Real.sin_sq_add_cos_sq θ]
  rw [Complex.normSq_eq_norm_sq] at h
  nlinarith [norm_nonneg (unit θ)]

private theorem normal_eq_I_unit (θ : ℝ) : normal θ = I * unit θ := by
  apply Complex.ext <;> simp [normal, unit, Complex.real_smul, Complex.mul_re, Complex.mul_im]

private theorem rotated_product (A B : ℂ →L[ℝ] ℝ) (θ : ℝ) :
    A (unit θ) * B (unit θ) + A (normal θ) * B (normal θ) = A 1 * B 1 + A I * B I := by
  simp only [unit, normal, map_add, map_smul, smul_eq_mul]
  linear_combination (A 1 * B 1 + A I * B I) * Real.sin_sq_add_cos_sq θ

private theorem along_base {f : ℂ → ℝ} {p : Chart} (hf : DifferentiableAt ℝ f p.1)
    (P : Chart → Chart) : along P (fun y : Chart => f y.1) p = fderiv ℝ f p.1 (P p).1 := by
  unfold along
  have d := hf.hasFDerivAt.comp p baseCLM.hasFDerivAt
  change HasFDerivAt (fun y : Chart => f y.1) _ p at d
  rw [d.fderiv]
  rfl

/-- Twice differentiating a base function by either horizontal field gives
its metric Hessian on the projected unit vector. The intermediate formula
keeps the angular derivative of the base velocity. -/
private theorem twice_horizontal {σ f : ℂ → ℝ} (hs : ContDiff ℝ ∞ σ) (hf : ContDiff ℝ ∞ f)
    (P : Chart → Chart) (u n : ℝ → ℂ) (p : Chart)
    (base : ∀ y : Chart, (P y).1 = scale σ y • u y.2.1)
    (angle : (P p).2.1 = scale σ p * fderiv ℝ σ p.1 (n p.2.1))
    (du : HasDerivAt u (n p.2.1) p.2.1) (hu : ‖u p.2.1‖ = 1)
    (orth : fderiv ℝ σ p.1 (u p.2.1) * fderiv ℝ f p.1 (u p.2.1) +
      fderiv ℝ σ p.1 (n p.2.1) * fderiv ℝ f p.1 (n p.2.1) =
        fderiv ℝ σ p.1 1 * fderiv ℝ f p.1 1 + fderiv ℝ σ p.1 I * fderiv ℝ f p.1 I) :
    along P (along P (fun y : Chart => f y.1)) p = unitHessian σ f p.1 (u p.2.1) := by
  have first : along P (fun y : Chart => f y.1) =
      fun y => scale σ y * fderiv ℝ f y.1 (u y.2.1) := by
    funext y
    rw [along_base (hf.differentiable (by simp) _), base, map_smul, smul_eq_mul]
  have ds := (hs.differentiable (by simp) p.1).hasFDerivAt.comp p baseCLM.hasFDerivAt
  have df := ((hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp) p.1).hasFDerivAt
  have dU := du.hasFDerivAt.comp p angleCLM.hasFDerivAt
  have d := ds.neg.exp.mul ((df.comp p baseCLM.hasFDerivAt).clm_apply dU)
  change HasFDerivAt (fun y => scale σ y * fderiv ℝ f y.1 (u y.2.1)) _ p at d
  have second : fderiv ℝ (fun y => fderiv ℝ f y (u p.2.1)) p.1 (u p.2.1) =
      fderiv ℝ (fderiv ℝ f) p.1 (u p.2.1) (u p.2.1) := by
    rw [(df.clm_apply (hasFDerivAt_const (u p.2.1) p.1)).fderiv]; simp
  have expEq : Real.exp (-2 * σ p.1) = (scale σ p)^2 := by
    unfold scale; rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [first, along, d.fderiv, unitHessian, conformalHessian, second, expEq, hu, ← orth]
  simp only [baseCLM, angleCLM, Function.comp_apply, base, angle, scale, Pi.neg_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', ContinuousLinearMap.toSpanSingleton_apply, map_smul, smul_eq_mul]
  ring

private theorem along_neglog {b : Chart → ℝ} (P : Chart → Chart) {p : Chart}
    (db : DifferentiableAt ℝ b p) (hp : b p ≠ 0) :
    along P (fun y => -Real.log (b y)) p = -along P b p / b p := by
  have d := (db.hasFDerivAt.log hp).neg
  change HasFDerivAt (fun y => -Real.log (b y)) _ p at d
  rw [along, d.fderiv]
  simp [along, div_eq_inv_mul]

private theorem twice_neglog {b : Chart → ℝ} (P : Chart → Chart) {p : Chart}
    (db : ContDiff ℝ ∞ b) (dP : DifferentiableAt ℝ P p) (hp : b p ≠ 0) :
    along P (along P (fun y => -Real.log (b y))) p =
      -along P (along P b) p / b p + (along P b p / b p)^2 := by
  have eq : along P (fun y => -Real.log (b y)) =ᶠ[𝓝 p] fun y => -(along P b y) / b y := by
    filter_upwards [db.continuous.continuousAt.eventually_ne hp] with y hy
    exact along_neglog _ (db.differentiable (by simp) _) hy
  have df := ((db.fderiv_right (m := ∞) (by simp)).differentiable (by simp) p).clm_apply dP
  change DifferentiableAt ℝ (along P b) p at df
  have d := df.hasFDerivAt.neg.mul ((hasDerivAt_inv hp).comp_hasFDerivAt p (db.differentiable (by simp) p).hasFDerivAt)
  change HasFDerivAt (fun y => -along P b y * (b y)⁻¹) _ p at d
  change fderiv ℝ _ p (P p) = _
  rw [eq.fderiv_eq]
  simp only [div_eq_mul_inv, d.fderiv]
  simp [along]
  field_simp
  ring

theorem smooth_defining (L : ℝ) : ContDiff ℝ ∞ (defining L) := by
  have hb : ContDiff ℝ ∞ b₀ := by
    rw [funext b₀_eq]
    exact contDiff_const.sub ((reCLM.contDiff.pow 2).add (imCLM.contDiff.pow 2))
  exact hb.sub (contDiff_const.mul (hb.pow 2))

/-- The side jet calculated using the coordinate Hessian coincides with
the actual list of differentiated polar-frame coefficients. -/
theorem polar_base_jet {σ : ℂ → ℝ} (hs : ContDiff ℝ ∞ σ) (L : ℝ) (p : Chart)
    (hp : defining L p.1 ≠ 0) :
    jet (frame σ) (fun y : Chart => -Real.log (defining L y.1)) p =
      sideJet σ L p.1 (unit p.2.1) := by
  let b := fun y : Chart => defining L y.1
  let θ := p.2.1
  have db : ContDiff ℝ ∞ b := (smooth_defining L).comp contDiff_fst
  have dunit (t : ℝ) : HasDerivAt unit (normal t) t :=
    ((Real.hasDerivAt_cos t).smul_const (1 : ℂ)).add ((Real.hasDerivAt_sin t).smul_const I)
  have dnormal (t : ℝ) : HasDerivAt normal (-unit t) t := by
    simpa only [unit, normal, neg_smul, neg_add, neg_neg] using
      (((Real.hasDerivAt_sin t).neg).smul_const (1 : ℂ)).add ((Real.hasDerivAt_cos t).smul_const I)
  have ortho := rotated_product (fderiv ℝ σ p.1) (fderiv ℝ (defining L) p.1) θ
  have d₁ (P : Chart → Chart) (v : ℂ) (hP : (P p).1 = scale σ p • v) :
      along P b p = unitSlope σ (defining L) p.1 v := by
    rw [along_base ((smooth_defining L).differentiable (by simp) _) P, hP, map_smul, smul_eq_mul]
    rfl
  have dx := d₁ (X σ) (unit θ) rfl
  have dh := d₁ (H σ) (normal θ) rfl
  have dxx := twice_horizontal hs (smooth_defining L) (X σ) unit normal p (fun _ => rfl) rfl
    (dunit θ) (norm_unit θ) ortho
  have dhh := twice_horizontal hs (smooth_defining L) (H σ) normal (fun t => -unit t) p
    (fun _ => rfl) rfl (dnormal θ) (by rw [normal_eq_I_unit]; simp [norm_unit]) (by
      simp only [map_neg, neg_mul_neg]
      linarith only [ortho])
  have vzero : along V (fun y : Chart => -Real.log (b y)) =ᶠ[𝓝 p] fun _ => 0 := by
    filter_upwards [db.continuous.continuousAt.eventually_ne hp] with y hy
    rw [along_neglog _ (db.differentiable (by simp) _) hy]
    dsimp only [b]
    rw [along_base ((smooth_defining L).differentiable (by simp) _)]
    simp [V]
  have dz (P : Chart → Chart) : along P (along V (fun y : Chart => -Real.log (b y))) p = 0 := by
    simp [along, vzero.fderiv_eq]
  have ⟨sX,sH⟩ := smooth_XH hs
  unfold jet sideJet LeviBoundary.baseJet
  rw [← normal_eq_I_unit]
  simp only [frame]
  rw [← show (fun y : Chart => -Real.log (b y)) = (fun y : Chart => -Real.log (defining L y.1)) by rfl]
  rw [twice_neglog _ db (sX.differentiable (by simp) _) hp, twice_neglog _ db (sH.differentiable (by simp) _) hp,
    along_neglog _ (db.differentiable (by simp) _) hp, along_neglog _ (db.differentiable (by simp) _) hp,
    dx, dh, dxx, dhh, dz, dz, dz]

/-- The actual exterior derivative of the base branch is strictly positive
in every nonzero direction of the polar chart, uniformly in the open fibre. -/
theorem positive_polar_base {σ : ℂ → ℝ} (simple : SimpleMetric σ) :
    ∃ L > 0, ∃ N : Set ℂ, IsOpen N ∧ sphere (0 : ℂ) 1 ⊆ N ∧
      ∀ p : Chart, p.1 ∈ N → ‖p.1‖ < 1 → p.2.2 < 0 → ∀ w : Chart, w ≠ 0 →
        0 < ddC (J σ) (potential (frame σ) (fun y => -Real.log (defining L y.1))) p w (J σ p w) := by
  obtain ⟨L, hL, N, hN, hs, hcollar⟩ := exists_positive_side simple
  refine ⟨L, hL, N, hN, hs, ?_⟩
  intro p hp hbase hrad w hw
  obtain ⟨hb, hside⟩ := hcollar p.1 hp hbase
  let b := fun y : Chart => defining L y.1
  have db : ContDiff ℝ ∞ b := (smooth_defining L).comp contDiff_fst
  have ht := (equationsAt simple.smooth p hrad).positive
  have ht' : t p < 1 := by
    dsimp [t, ConformalFrame.radialParameter]
    apply (div_lt_one (by positivity)).mpr
    linarith [Real.exp_pos (2*p.2.2)]
  obtain ⟨hB,hS⟩ := hside (unit p.2.1) (norm_unit _) (t p) ht ht'
  rw [← polar_base_jet simple.smooth L p hb.ne'] at hB hS
  apply ConformalFrame.positive_of_schur simple.smooth p hrad
    ((db.contDiffAt.log hb.ne').neg.of_le (by decide)) _ hB hS hw
  filter_upwards [db.continuous.continuousAt.eventually_ne hb.ne'] with y hy
  rw [along_neglog _ (db.differentiable (by simp) _) hy,
    along_base ((smooth_defining L).differentiable (by simp) _)]
  simp [R]

end Polar
end TransportOkaGrauert.ConformalCollar
