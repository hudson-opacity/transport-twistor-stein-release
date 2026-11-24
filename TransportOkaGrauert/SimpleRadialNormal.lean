import TransportOkaGrauert.SimpleRadialStar
import TransportOkaGrauert.SimpleRadialInverse
import TransportOkaGrauert.ChartJacobi

/-! # Inverting an endpoint map using its angular Jacobi field

The endpoint differential in the radial direction is read directly from the
unit-speed equation. Its angular direction is the normal Jacobi variation.
The no-conjugate-points and convexity assumptions then suffice for global
smooth inversion of the endpoint map throughout the open disk.
-/

noncomputable section
namespace TransportOkaGrauert.SimpleRadialNormal
open Complex Set Metric SimpleDiskTarget SimpleRadialStar
open scoped ContDiff Topology

private theorem polar_bijective {A : ℂ →L[ℝ] ℂ} {x w : ℂ}
    (hx : x ≠ 0) (hw : w ≠ 0) {r s : ℝ} (hr : r ≠ 0) (hs : s ≠ 0)
    (rad : A x = r • w) (ang : A (I*x) = s • (I*w)) : Function.Bijective A := by
  have vec (z : ℂ) : z = (z/x).re • x + (z/x).im • (I*x) := by
    calc
      z = (z/x) * x := (div_mul_cancel₀ _ hx).symm
      _ = _ := by
        conv_lhs => arg 1; rw [← Complex.re_add_im (z/x)]
        simp only [Complex.real_smul, add_mul, mul_assoc]
  have trivialKer (z : ℂ) (hz : A z = 0) : z = 0 := by
    rw [vec z, map_add, map_smul, map_smul, rad, ang] at hz
    have eq : (((z/x).re * r : ℝ) + ((z/x).im * s : ℝ) * I : ℂ) * w = 0 := by
      simpa [Complex.real_smul, add_mul, mul_assoc] using hz
    have ez := (mul_eq_zero.mp eq).resolve_right hw
    have h1 : (z/x).re = 0 := (mul_eq_zero.mp (by simpa using congrArg Complex.re ez :
      (z/x).re*r = 0)).resolve_right hr
    have h2 : (z/x).im = 0 := (mul_eq_zero.mp (by simpa using congrArg Complex.im ez :
      (z/x).im*s = 0)).resolve_right hs
    rw [vec z, h1, h2, zero_smul, zero_smul, add_zero]
  have inj : Function.Injective A := by
    intro a b hh
    exact sub_eq_zero.mp (trivialKer _ (by rw [map_sub,hh,sub_self]))
  exact ⟨inj, LinearMap.injective_iff_surjective.mp (show Function.Injective A.toLinearMap from inj)⟩

private theorem radial_column {f : ℂ → ℂ} {σ : ℂ → ℝ} {x : ℂ} {θ : ℝ → ℝ}
    (hx : x ≠ 0) (hf : DifferentiableAt ℝ f x) (ray : unitGeodesicOn σ (along f x) θ (Icc 0 ‖x‖)) :
    fderiv ℝ f x x = (‖x‖ * Real.exp (-σ (f x))) • (Circle.exp (θ ‖x‖) : ℂ) := by
  let r := ‖x‖
  have hp : 0 < r := norm_pos_iff.mpr hx
  have atR : (r/r) • x = x := by simp [hp.ne']
  have inner := (((hasDerivAt_id r).div_const r).smul_const x)
  have comp := (show DifferentiableAt ℝ f ((r/r) • x) by rwa [atR]).hasFDerivAt.comp_hasDerivAt r inner
  have deriv := (ray r (right_mem_Icc.mpr hp.le)).1
  have un := uniqueDiffOn_Icc hp r (right_mem_Icc.mpr hp.le)
  have eq := (comp.hasDerivWithinAt.derivWithin un).symm.trans (deriv.derivWithin un)
  change fderiv ℝ f ((r/r) • x) ((1/r) • x) =
    ↑(Real.exp (-σ (f ((r/r) • x)))) * ↑(Circle.exp (θ r)) at eq
  rw [atR, map_smul] at eq
  calc
    fderiv ℝ f x x = r • ((1/r) • fderiv ℝ f x x) := by simp [hp.ne']
    _ = _ := by rw [eq]; simp [Complex.real_smul, r, mul_assoc]

/-- Existence of a global smooth log map for an interior centre. The ODE input
is a continuous endpoint map, smooth before exit, with nonsingular central jet
and angular variation governed by the normalized scalar Jacobi equation. No
global injectivity, smooth exit time, uniform escape time, nonvanishing Jacobi
field, or smooth inverse is assumed. -/
theorem smooth_log_of_jacobi_variation {σ : ℂ → ℝ} (simple : SimpleMetric σ)
    (f : ℂ → ℂ) (continuous : Continuous f) (centre : ‖f 0‖ < 1)
    (escapes : ∀ w : Circle, ∃ t : ℝ, 0 < t ∧ 1 < ‖f (t • (w : ℂ))‖)
    (smooth : ∀ x ∈ beforeExit f 1, ContDiffAt ℝ ∞ f x)
    (centralJet : Function.Bijective (fderiv ℝ f 0))
    (rays : ∀ x ∈ retained f 1, x ≠ 0 → ∃ θ,
      unitGeodesicOn σ (along f x) θ (Icc 0 ‖x‖) ∧
      ∃ j dj, jacobiOn σ (along f x) j dj (Icc 0 ‖x‖) ∧ j 0 = 0 ∧ dj 0 = 1 ∧
        fderiv ℝ f x (I*x) = (j ‖x‖ * Real.exp (-σ (f x))) • (I * (Circle.exp (θ ‖x‖) : ℂ))) :
    ∃ L : ℂ → ℂ, ContDiffOn ℝ ∞ L (ball (0 : ℂ) 1) ∧
      (∀ y ∈ ball (0 : ℂ) 1, L y ∈ retained f 1 ∧ f (L y) = y) ∧
      ∀ x ∈ retained f 1, f x ∈ ball (0 : ℂ) 1 → L (f x) = x := by
  have eq := retained_inter_preimage simple centre (fun x hx h => by
    obtain ⟨θ, ht, _⟩ := rays x hx h
    exact ⟨θ, ht⟩)
  apply SimpleRadialInverse.smooth_inverse_on_disk (by norm_num)
    (isCompact_retained continuous escapes) continuous.continuousOn
  · rw [eq]; exact isOpen_beforeExit continuous 1
  · rw [eq]; exact starConvex_beforeExit f 1
  · rw [eq]; exact fun t _ => by simpa using centre
  · rwa [eq]
  intro x hx
  by_cases h : x = 0
  · simpa [h] using centralJet
  obtain ⟨θ, ht, j, dj, oj, h0, h1, tang⟩ := rays x hx.1 h
  have rpos := norm_pos_iff.mpr h
  have jpos := ChartJacobi.normalized_jacobi_positive simple rpos ht (along_retained h hx.1) oj h0 h1
  exact polar_bijective h (Circle.coe_ne_zero _) (mul_pos rpos (Real.exp_pos _)).ne'
    (mul_pos jpos (Real.exp_pos _)).ne'
    (radial_column h ((smooth x (eq ▸ hx)).differentiableAt (by simp)) ht) tang

end TransportOkaGrauert.SimpleRadialNormal
