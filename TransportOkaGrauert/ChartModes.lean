import TransportOkaGrauert.DiskSeries
import TransportOkaGrauert.SimpleDiskTarget

/-! Disk extensions and multiplication for smooth chart gauges with unrestricted
nonnegative Fourier series. -/

noncomputable section
namespace TransportOkaGrauert.ChartModes
open SimpleDiskTarget Complex Metric Real
open scoped ContDiff ComplexConjugate

local instance : Fact (0 < 2 * π) := ⟨Real.two_pi_pos⟩

variable {n : ℕ}

theorem toCircle_angle (t : ℝ) : AddCircle.toCircle (t : DiskSeries.Angle) = Circle.exp t := by
  rw [AddCircle.toCircle_apply_mk]; simp [Real.pi_ne_zero]

theorem slice_smooth {F : Field n} (hs : SmoothToBoundary F) {z : ℂ} (hz : z ∈ closedBall 0 1)
    (i j : Fin n) : ContDiff ℝ ∞ (fun t : ℝ => F z (Circle.exp t) i j) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  exact (hs z hz t i j).comp t (contDiffAt_const.prodMk contDiffAt_id)

/-- The shifted Fourier series of a smooth nonnegative-mode field gives an
actual holomorphic matrix extension on each closed fiber disk. -/
theorem matrix_extension (F : Field n) (hs : SmoothToBoundary F) (hm : ModesFrom 0 F)
    (z : ℂ) (hz : z ∈ closedBall 0 1) :
    ∃ b : ℂ → Mat n, (∀ i j, DiffContOnCl ℂ (fun w => b w i j) (ball 0 1)) ∧
      ∀ v : Circle, b v = F z v := by
  have each (i j : Fin n) : ∃ b : ℂ → ℂ, DiffContOnCl ℂ b (ball 0 1) ∧
      ∀ v : Circle, b v = F z v i j := by
    let a : DiskSeries.Angle → ℂ := fun θ => conj (θ.toCircle : ℂ) * F z θ.toCircle i j
    have hsm : ContDiff ℝ 2 (fun t : ℝ => a t) := by
      change ContDiff ℝ 2 (fun t : ℝ => conj (AddCircle.toCircle (t : DiskSeries.Angle) : ℂ) *
        F z (AddCircle.toCircle (t : DiskSeries.Angle)) i j)
      simp only [toCircle_angle]
      apply ContDiff.mul _ ((slice_smooth hs hz i j).of_le (by decide))
      apply Complex.conjCLE.contDiff.comp
      convert (contDiff_circleMap 0 1 (n := 2)) using 1
      funext t
      simp [circleMap, Circle.coe_exp]
    let bnd : C(DiskSeries.Angle, ℂ) := ⟨a, continuous_coinduced_dom.mpr hsm.continuous⟩
    have hsup (k : ℤ) (hk : k < -1) : fourierCoeff bnd k = 0 := by
      change fourierCoeff (fun θ : DiskSeries.Angle => conj (θ.toCircle : ℂ) * F z θ.toCircle i j) k = 0
      rw [BoundaryModes.conjugate_shift]
      exact hm z hz i j _ (by omega)
    obtain ⟨b, hb, htrace⟩ := (DiskSeries.admissible_iff_diskExtension bnd hsm).mp hsup
    refine ⟨b, hb, ?_⟩
    intro v
    let θ : DiskSeries.Angle := (arg (v : ℂ) : ℝ)
    have hθ : θ.toCircle = v := (toCircle_angle _).trans (Circle.exp_arg v)
    have he := htrace θ
    change conj (θ.toCircle : ℂ) * b θ.toCircle = conj (θ.toCircle : ℂ) * F z θ.toCircle i j at he
    rw [hθ] at he
    exact mul_left_cancel₀ (by simp) he
  choose b hreg htrace using each
  exact ⟨fun w i j => b i j w, hreg, fun v => Matrix.ext fun i j => htrace i j v⟩

theorem smooth_mul {F G : Field n} (hf : SmoothToBoundary F) (hg : SmoothToBoundary G) :
    SmoothToBoundary (F * G) := by
  intro z hz θ i j
  change ContDiffAt ℝ ∞ (fun p : ℂ × ℝ => ∑ k, F p.1 (Circle.exp p.2) i k * G p.1 (Circle.exp p.2) k j) _
  exact ContDiffAt.sum fun k _ => (hf z hz θ i k).mul (hg z hz θ k j)

/-- Infinite smooth holomorphic-mode matrix fields form a multiplicative class. -/
theorem modes_mul {F G : Field n} (hf : SmoothToBoundary F) (hg : SmoothToBoundary G)
    (hf₀ : ModesFrom 0 F) (hg₀ : ModesFrom 0 G) : ModesFrom 0 (F * G) := by
  intro z hz i j k hk
  obtain ⟨f, hfr, hft⟩ := matrix_extension F hf hf₀ z hz
  obtain ⟨g, hgr, hgt⟩ := matrix_extension G hg hg₀ z hz
  let b := fun w : ℂ => (f w * g w) i j
  have hr : DiffContOnCl ℂ b (ball 0 1) := by
    change DiffContOnCl ℂ (fun w => ∑ l, f w i l * g w l j) _
    exact ⟨DifferentiableOn.fun_sum (fun l _ => (hfr i l).differentiableOn.mul (hgr l j).differentiableOn),
      continuousOn_finset_sum _ (fun l _ => (hfr i l).continuousOn.mul (hgr l j).continuousOn)⟩
  have he : (fun θ : DiskSeries.Angle => (F * G) z θ.toCircle i j) = BoundaryModes.boundaryTrace b := by
    funext θ
    simp [BoundaryModes.boundaryTrace, b, hft, hgt]
  rw [he]
  exact BoundaryModes.negativeMode_eq_zero hr k hk

end TransportOkaGrauert.ChartModes
