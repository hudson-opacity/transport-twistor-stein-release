import TransportOkaGrauert.ChartModes
import TransportOkaGrauert.Orbits
import Mathlib.Analysis.Calculus.TangentCone.Real

/-! Relative holomorphic frames for the chart geodesic operator. -/

noncomputable section
namespace TransportOkaGrauert.ChartOrbits
open SimpleDiskTarget ChartModes Isothermal Metric Set
open scoped ContDiff

variable {n : ℕ}

/-- Apply the isothermal geodesic field entrywise. -/
def chartX (lam : ℂ → ℝ) (F : Field n) : Field n :=
  fun z v i j => geodesicX lam (fun p w => F p w i j) z v

/-- A relative holomorphic frame from attenuation A to attenuation B. -/
structure RelativeFrame (lam : ℂ → ℝ) (A B F G : Field n) : Prop where
  smoothF : SmoothToBoundary F
  smoothG : SmoothToBoundary G
  modesF : ModesFrom 0 F
  modesG : ModesFrom 0 G
  inverses : ∀ z ∈ closedBall (0 : ℂ) 1, ∀ v : Circle,
    F z v * G z v = 1 ∧ G z v * F z v = 1
  transport : ∀ z ∈ closedBall (0 : ℂ) 1, ∀ v : Circle,
    chartX lam F z v + A z v * F z v = F z v * B z v

private theorem base_diff {F : Field n} (h : SmoothToBoundary F) {z : ℂ} (hz : z ∈ closedBall 0 1)
    (v : Circle) (i j : Fin n) : DifferentiableAt ℝ (fun p => F p v i j) z := by
  obtain ⟨θ, rfl⟩ : ∃ θ, Circle.exp θ = v := ⟨_, Circle.exp_arg v⟩
  exact ((h z hz θ i j).comp z (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by decide)

private theorem angle_diff {F : Field n} (h : SmoothToBoundary F) {z : ℂ} (hz : z ∈ closedBall 0 1)
    (v : Circle) (i j : Fin n) :
    DifferentiableAt ℝ (fun t : ℝ => F z (v * Circle.exp t) i j) 0 := by
  obtain ⟨θ, rfl⟩ : ∃ θ, Circle.exp θ = v := ⟨_, Circle.exp_arg v⟩
  simp_rw [← Circle.exp_add]
  exact ((slice_smooth h hz i j).comp (contDiff_const.add contDiff_id)).differentiable (by decide) 0

theorem chartX_mul (lam : ℂ → ℝ) {F G : Field n} (hf : SmoothToBoundary F) (hg : SmoothToBoundary G)
    {z : ℂ} (hz : z ∈ closedBall 0 1) (v : Circle) :
    chartX lam (F * G) z v = chartX lam F z v * G z v + F z v * chartX lam G z v := by
  ext i j
  have hfb k := base_diff hf hz v i k
  have hgb k := base_diff hg hz v k j
  have hfa k := angle_diff hf hz v i k
  have hga k := angle_diff hg hz v k j
  simp only [chartX, Pi.mul_apply, Matrix.add_apply, Matrix.mul_apply, geodesicX,
    Fourier.flatX, vertical]
  rw [fderiv_fun_sum (A := fun k p => F p v i k * G p v k j) (fun k _ => (hfb k).mul (hgb k)),
    deriv_fun_sum (A := fun k t => F z (v * Circle.exp t) i k * G z (v * Circle.exp t) k j)
      (fun k _ => (hfa k).mul (hga k))]
  simp only [ContinuousLinearMap.sum_apply, fderiv_fun_mul (hfb _) (hgb _),
    deriv_fun_mul (hfa _) (hga _), ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, Circle.exp_zero, mul_one]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intros
  ring

private theorem smooth_one : SmoothToBoundary (1 : Field n) :=
  fun _ _ _ _ _ => contDiffAt_const

private theorem modes_one : ModesFrom 0 (1 : Field n) := by
  intro z hz i j k hk
  apply BoundaryModes.negativeMode_eq_zero (f := fun _ => (1 : Mat n) i j) diffContOnCl_const k hk

@[simp] theorem chartX_one (lam : ℂ → ℝ) (z : ℂ) (w : Circle) :
    chartX lam (1 : Field n) z w = 0 := by
  ext i j
  change geodesicX lam (fun _ _ => (1 : Mat n) i j) z w = 0
  simp [geodesicX, Fourier.flatX, vertical]

theorem chartX_eq {lam : ℂ → ℝ} {F G : Field n} (hf : SmoothToBoundary F)
    (hg : SmoothToBoundary G) (he : ∀ z ∈ closedBall (0 : ℂ) 1, ∀ v : Circle, F z v = G z v)
    {z : ℂ} (hz : z ∈ closedBall 0 1) (v : Circle) :
    chartX lam F z v = chartX lam G z v := by
  have hu : UniqueDiffOn ℝ (closedBall (0 : ℂ) 1) :=
    uniqueDiffOn_convex (convex_closedBall _ _)
      ⟨0, by rw [interior_closedBall _ (by norm_num : (1 : ℝ) ≠ 0)]; exact mem_ball_self (by norm_num)⟩
  ext i j
  have eqbase : fderiv ℝ (fun p => F p v i j) z = fderiv ℝ (fun p => G p v i j) z := by
    rw [← (base_diff hf hz v i j).fderivWithin (hu z hz),
      ← (base_diff hg hz v i j).fderivWithin (hu z hz)]
    apply fderivWithin_congr
    · exact fun p hp => congrArg (fun M : Mat n => M i j) (he p hp v)
    · exact congrArg (fun M : Mat n => M i j) (he z hz v)
  have eqa : (fun t : ℝ => F z (v * Circle.exp t) i j) =
      fun t => G z (v * Circle.exp t) i j := funext fun t =>
    congrArg (fun M : Mat n => M i j) (he z hz _)
  simp only [chartX, geodesicX, Fourier.flatX, vertical, eqbase, eqa]

variable {lam : ℂ → ℝ} {A B C F G J K : Field n}

theorem RelativeFrame.refl (lam : ℂ → ℝ) (A : Field n) :
    RelativeFrame lam A A 1 1 :=
  ⟨smooth_one, smooth_one, modes_one, modes_one, by simp, by simp⟩

theorem RelativeFrame.trans (h : RelativeFrame lam A B F G) (k : RelativeFrame lam B C J K) :
    RelativeFrame lam A C (F * J) (K * G) := by
  refine ⟨smooth_mul h.smoothF k.smoothF, smooth_mul k.smoothG h.smoothG,
    modes_mul h.smoothF k.smoothF h.modesF k.modesF, modes_mul k.smoothG h.smoothG k.modesG h.modesG,
    ?_, ?_⟩
  · intro z hz v
    obtain ⟨hfg,hgf⟩ := h.inverses z hz v
    obtain ⟨hjk,hkj⟩ := k.inverses z hz v
    simp only [Pi.mul_apply]
    constructor
    · calc
        _ = F z v * (J z v * K z v) * G z v := by simp only [mul_assoc]
        _ = _ := by rw [hjk, mul_one, hfg]
    · calc
        _ = K z v * (G z v * F z v) * J z v := by simp only [mul_assoc]
        _ = _ := by rw [hgf, mul_one, hkj]
  · intro z hz v
    rw [chartX_mul lam h.smoothF k.smoothF hz v]
    simp only [Pi.mul_apply]
    calc
      _ = (chartX lam F z v + A z v * F z v) * J z v + F z v * chartX lam J z v := by noncomm_ring
      _ = F z v * (chartX lam J z v + B z v * J z v) := by rw [h.transport z hz v]; noncomm_ring
      _ = _ := by rw [k.transport z hz v, mul_assoc]

theorem RelativeFrame.symm (h : RelativeFrame lam A B F G) : RelativeFrame lam B A G F := by
  refine ⟨h.smoothG, h.smoothF, h.modesG, h.modesF, fun z hz v => (h.inverses z hz v).symm, ?_⟩
  intro z hz v
  obtain ⟨hfg,hgf⟩ := h.inverses z hz v
  have hconstant := chartX_eq (lam := lam) (smooth_mul h.smoothF h.smoothG) smooth_one
    (fun p hp w => (h.inverses p hp w).1) hz v
  rw [chartX_mul lam h.smoothF h.smoothG hz v, chartX_one] at hconstant
  have hx := h.transport z hz v
  have key : F z v * (chartX lam G z v + B z v * G z v) = F z v * (G z v * A z v) := by
    calc
      _ = F z v * chartX lam G z v + (F z v * B z v) * G z v := by noncomm_ring
      _ = (chartX lam F z v * G z v + F z v * chartX lam G z v) + A z v * (F z v * G z v) := by
        rw [← hx]; noncomm_ring
      _ = _ := by rw [hconstant, zero_add, hfg, mul_one, ← mul_assoc, hfg, one_mul]
  simpa only [← mul_assoc, hgf, one_mul] using congrArg (G z v * ·) key

/-- Orbit equivalence on any parametrized family, using the actual chart
PDE and smooth holomorphic gauges on the closed disk. -/
def relativeSetoid {P : Type*} (lam : ℂ → ℝ) (family : P → Field n) : Setoid P where
  r s t := ∃ F G, RelativeFrame lam (family s) (family t) F G
  iseqv := {
    refl := fun s => ⟨1, 1, RelativeFrame.refl lam (family s)⟩
    symm := by rintro _ _ ⟨F, G, h⟩; exact ⟨G, F, h.symm⟩
    trans := by rintro _ _ _ ⟨F, G, h⟩ ⟨J, K, h'⟩; exact ⟨F*J, K*G, h.trans h'⟩ }

/-- Local solvability in a connected parameter family implies global relative
frames between every pair of parameters. -/
theorem relative_of_local {P : Type*} [TopologicalSpace P] [PreconnectedSpace P]
    (lam : ℂ → ℝ) (family : P → Field n)
    (localFrames : ∀ t, ∃ V : Set P, IsOpen V ∧ t ∈ V ∧ ∀ s ∈ V, ∃ F G,
      RelativeFrame lam (family t) (family s) F G) (t s : P) :
    ∃ F G, RelativeFrame lam (family t) (family s) F G :=
  related_of_open_classes (relativeSetoid lam family)
    (open_classes_of_local_reachability (relativeSetoid lam family) localFrames) t s

theorem RelativeFrame.toFrame {lam : ℂ → ℝ} {A F G : Field n} (h : RelativeFrame lam A 0 F G) :
    IsFrame lam A F G := by
  refine ⟨h.smoothF, h.smoothG, h.modesF, h.modesG, h.inverses, ?_⟩
  intro z hz w i j
  have ht := congrArg (fun M : Mat n => M i j) (h.transport z hz w)
  simpa [chartX] using ht

/-- It suffices to produce relative frames locally along the one-parameter
family tA, including one-sided neighborhoods at its endpoints. -/
theorem frame_of_local_along_ray (lam : ℂ → ℝ) (A : Field n)
    (localFrames : ∀ t : Set.Icc (0 : ℝ) 1, ∃ V : Set (Set.Icc (0 : ℝ) 1),
      IsOpen V ∧ t ∈ V ∧ ∀ s ∈ V, ∃ F G,
        RelativeFrame lam ((t : ℝ) • A) ((s : ℝ) • A) F G) :
    ∃ F G, IsFrame lam A F G := by
  obtain ⟨F, G, h⟩ := relative_of_local lam (fun t : Set.Icc (0 : ℝ) 1 => (t : ℝ) • A)
    localFrames 1 0
  have h' : RelativeFrame lam A 0 F G := by simpa using h
  exact ⟨F, G, h'.toFrame⟩

end TransportOkaGrauert.ChartOrbits
