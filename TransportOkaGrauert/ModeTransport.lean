import TransportOkaGrauert.CoefficientBridge
import TransportOkaGrauert.SmoothCoefficient

/-! The mixed chart transport equation as a tridiagonal system on the actual
base-dependent Haar coefficients. The two exceptional equations at the edge
of the nonnegative spectrum describe the obstruction to projection. -/

noncomputable section
namespace TransportOkaGrauert.ModeTransport

open SimpleDiskTarget SkewReduction MixedCorrection ChartCoefficients ChartModes
open Complex Metric
open scoped ContDiff
variable {n : ℕ}
local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

/-- Index first, so each input to the differential operator is a base field. -/
abbrev modes (U : Field n) (k : ℤ) (z : ℂ) : Mat n := modeMatrix U z k

/-- Differential contribution from an input of frequency l displaced by
q = +1 or −1. The second base derivative direction is i. -/
def geodesicTerm (lam : ℂ → ℝ) (q l : ℤ) (a : ℂ → Mat n) (z : ℂ) : Mat n :=
  fun i j => (Real.exp (-lam z) : ℂ) *
    ((1/2 : ℂ) * fderiv ℝ (fun p => a p i j) z 1 +
      ((q : ℂ)/(2*I)) * fderiv ℝ (fun p => a p i j) z I +
      driftWeight lam z q * (I * (l : ℂ) * a z i j))

/-- The left and right matrix multiplications from one attenuation mode. -/
def attenuationTerm (A : Field n) (t s : ℝ) (q : ℤ) (a : Mat n) (z : ℂ) : Mat n :=
  t • (modeMatrix A z q * a) - s • (a * modeMatrix A z q)

/-- Raising and lowering terms, indexed by shift and input frequency. -/
def offDiagonal (lam : ℂ → ℝ) (A : Field n) (t s : ℝ) (q l : ℤ)
    (a : ℂ → Mat n) (z : ℂ) : Mat n :=
  geodesicTerm lam q l a z + attenuationTerm A t s q (a z) z

/-- The complete coefficient at output frequency k. -/
def transport (lam : ℂ → ℝ) (A : Field n) (t s : ℝ) (u : ℤ → ℂ → Mat n)
    (k : ℤ) (z : ℂ) : Mat n :=
  offDiagonal lam A t s 1 (k-1) (u (k-1)) z + attenuationTerm A t s 0 (u k z) z +
    offDiagonal lam A t s (-1) (k+1) (u (k+1)) z

theorem mode_derivX (lam : ℂ → ℝ) {U : Field n} (hu : SmoothToBoundary U)
    {z : ℂ} (hz : z ∈ closedBall 0 1) (k : ℤ) :
    modes (derivX lam U) k z = geodesicTerm lam 1 (k-1) (modes U (k-1)) z +
      geodesicTerm lam (-1) (k+1) (modes U (k+1)) z := by
  ext i j
  let f := fun p v => U p v i j
  have h := coefficient_geodesicX lam f z k
    (fun θ => (hu z hz θ i j).of_le (by decide))
    ((slice_smooth hu hz i j).of_le (by decide))
  change coefficient (Isothermal.geodesicX lam f) k z = _
  rw [h, mul_add]
  simp only [neighbor, geodesicTerm, Matrix.add_apply, Int.cast_one, Int.cast_neg]
  rfl

/-- The full chart PDE is equivalent to the explicit neighboring-mode
equations. The rank, conformal factor, and spectrum of U are unrestricted. -/
theorem solves_iff_neighbors {lam : ℂ → ℝ} {A U : Field n} (t s : ℝ)
    (ha : SmoothToBoundary A) (hu : SmoothToBoundary U) (hm : ThreeModes A) :
    Solves lam A U t s ↔ ∀ z ∈ closedBall (0 : ℂ) 1, ∀ k : ℤ,
      transport lam A t s (modes U) k z = -modes A k z := by
  rw [CoefficientBridge.solves_iff_coefficients t s ha hu]
  apply forall_congr'; intro z
  apply forall_congr'; intro hz
  apply forall_congr'; intro k
  change (modes (derivX lam U) k z + _ - _ = _) ↔ _
  rw [mode_derivX lam hu hz, mode_left_mul ha hu hm z hz, mode_right_mul ha hu hm z hz]
  simp only [transport, offDiagonal, attenuationTerm, modes, smul_add]
  abel_nf

private theorem offDiagonal_congr {lam : ℂ → ℝ} {A : Field n} {t s : ℝ} {q l : ℤ}
    {a b : ℂ → Mat n} {z : ℂ} (hz : z ∈ closedBall 0 1)
    (h : Set.EqOn a b (closedBall (0 : ℂ) 1))
    (ha : ∀ i j, DifferentiableAt ℝ (fun x => a x i j) z)
    (hb : ∀ i j, DifferentiableAt ℝ (fun x => b x i j) z) :
    offDiagonal lam A t s q l a z = offDiagonal lam A t s q l b z := by
  have huniq : UniqueDiffWithinAt ℝ (closedBall (0 : ℂ) 1) z :=
    uniqueDiffOn_convex (convex_closedBall _ _) ⟨0, by
      rw [interior_closedBall _ (by norm_num : (1 : ℝ) ≠ 0)]
      exact mem_ball_self (by norm_num)⟩ z hz
  have hd (i j : Fin n) : fderiv ℝ (fun x => a x i j) z = fderiv ℝ (fun x => b x i j) z := by
    rw [← (ha i j).fderivWithin huniq, ← (hb i j).fderivWithin huniq]
    apply fderivWithin_congr
    · intro x hx
      exact congrArg (fun M : Mat n => M i j) (h hx)
    · exact congrArg (fun M : Mat n => M i j) (h hz)
  ext i j
  simp only [offDiagonal, Matrix.add_apply, geodesicTerm, hd, h hz]

private theorem offDiagonal_zero (lam : ℂ → ℝ) (A : Field n) (t s : ℝ) (q l : ℤ) (z : ℂ) :
    offDiagonal lam A t s q l (fun _ => 0) z = 0 := by
  ext i j
  simp [offDiagonal, geodesicTerm, attenuationTerm]

/-- Truncate a smooth unrestricted solution to nonnegative frequencies.
The truncation solves the same transport equation exactly when two
discarded terms vanish, in output frequencies −1 and 0. Equality of the
truncated coefficients is required only on the disk. -/
theorem projected_solves_iff_two_defects {lam : ℂ → ℝ} {A U P : Field n} {t s : ℝ}
    (ha : SmoothToBoundary A) (hu : SmoothToBoundary U) (hp : SmoothToBoundary P)
    (hm : ThreeModes A) (hs : Solves lam A U t s)
    (proj : ∀ z ∈ closedBall (0 : ℂ) 1, ∀ k : ℤ,
      modes P k z = if 0 ≤ k then modes U k z else 0) :
    Solves lam A P t s ↔ ∀ z ∈ closedBall (0 : ℂ) 1,
      offDiagonal lam A t s 1 (-2) (modes U (-2)) z +
        attenuationTerm A t s 0 (modes U (-1) z) z = 0 ∧
      offDiagonal lam A t s 1 (-1) (modes U (-1)) z = 0 := by
  have he := (solves_iff_neighbors t s ha hu hm).mp hs
  have hmode {F : Field n} (hF : SmoothToBoundary F) (l : ℤ) {z : ℂ} (hz : z ∈ closedBall 0 1)
      (i j : Fin n) : DifferentiableAt ℝ (fun x => modes F l x i j) z :=
    (SmoothCoefficient.smooth_mode hF hz l i j).differentiableAt (by decide)
  have hoff (z : ℂ) (hz : z ∈ closedBall 0 1) (q l : ℤ) :
      offDiagonal lam A t s q l (modes P l) z =
        if 0 ≤ l then offDiagonal lam A t s q l (modes U l) z else 0 := by
    by_cases h : 0 ≤ l
    · rw [if_pos h]
      exact offDiagonal_congr hz (fun y hy => by simpa [h] using proj y hy l)
        (hmode hp l hz) (hmode hu l hz)
    · rw [if_neg h, ← offDiagonal_zero lam A t s q l z]
      exact offDiagonal_congr hz (fun y hy => by simpa [h] using proj y hy l)
        (hmode hp l hz) (fun _ _ => differentiableAt_const _)
  have hmid (z : ℂ) (hz : z ∈ closedBall 0 1) (l : ℤ) :
      attenuationTerm A t s 0 (modes P l z) z =
        if 0 ≤ l then attenuationTerm A t s 0 (modes U l z) z else 0 := by
    rw [proj z hz]
    split <;> simp [attenuationTerm]
  have hedge (z : ℂ) (hz : z ∈ closedBall 0 1) :
      (offDiagonal lam A t s 1 (-2) (modes U (-2)) z + attenuationTerm A t s 0 (modes U (-1) z) z) +
        transport lam A t s (modes P) (-1) z = -modes A (-1) z := by
    rw [← he z hz]
    norm_num [transport, hoff z hz, hmid z hz]
  have hzero (z : ℂ) (hz : z ∈ closedBall 0 1) :
      offDiagonal lam A t s 1 (-1) (modes U (-1)) z + transport lam A t s (modes P) 0 z =
        -modes A 0 z := by
    rw [← he z hz]
    norm_num [transport, hoff z hz, hmid z hz, add_assoc]
  rw [solves_iff_neighbors t s ha hp hm]
  constructor
  · intro h z hz
    have hm₁ := hedge z hz
    have hz₀ := hzero z hz
    rw [h z hz (-1)] at hm₁
    rw [h z hz 0] at hz₀
    exact ⟨(add_left_inj _).mp (hm₁.trans (zero_add _).symm),
      (add_left_inj _).mp (hz₀.trans (zero_add _).symm)⟩
  · intro h z hz k
    obtain ⟨hm₁, hz₀⟩ := h z hz
    by_cases hn : k < -1
    · have ha0 : modes A k z = 0 := by ext i j; exact hm z hz i j k (Or.inl hn)
      simp [transport, hoff z hz, hmid z hz, ha0, show ¬ 1 ≤ k by omega,
        show ¬ 0 ≤ k by omega, show ¬ 0 ≤ k + 1 by omega]
    by_cases hneg : k = -1
    · subst k; simpa only [hm₁, zero_add] using hedge z hz
    by_cases h0 : k = 0
    · subst k; simpa only [hz₀, zero_add] using hzero z hz
    · rw [← he z hz]
      simp [transport, hoff z hz, hmid z hz, show 1 ≤ k by omega,
        show 0 ≤ k by omega, show 0 ≤ k + 1 by omega]

private theorem modes_add {U V : Field n} (hu : SmoothToBoundary U) (hv : SmoothToBoundary V)
    {z : ℂ} (hz : z ∈ closedBall 0 1) (l : ℤ) :
    modes (U+V) l z = modes U l z + modes V l z := by
  ext i j
  have hint {F : Field n} (hF : SmoothToBoundary F) :
      MeasureTheory.Integrable (fun θ : DiskSeries.Angle => F z θ.toCircle i j) AddCircle.haarAddCircle :=
    (entry_continuous hF z hz i j).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  exact congrFun (fourierCoeff.add (hint hu) (hint hv)) l

private theorem attenuation_add (A : Field n) (t s : ℝ) (q : ℤ) (a b : Mat n) (z : ℂ) :
    attenuationTerm A t s q (a+b) z = attenuationTerm A t s q a z + attenuationTerm A t s q b z := by
  simp only [attenuationTerm, mul_add, add_mul, smul_add]
  abel

private theorem offDiagonal_add {U V : Field n} (hu : SmoothToBoundary U) (hv : SmoothToBoundary V)
    (lam : ℂ → ℝ) (A : Field n) (t s : ℝ) (q l : ℤ) {z : ℂ} (hz : z ∈ closedBall 0 1) :
    offDiagonal lam A t s q l (modes (U+V) l) z =
      offDiagonal lam A t s q l (modes U l) z + offDiagonal lam A t s q l (modes V l) z := by
  have hUV : SmoothToBoundary (U+V) := fun x hx θ i j => (hu x hx θ i j).add (hv x hx θ i j)
  have hD {F : Field n} (hF : SmoothToBoundary F) (i j : Fin n) :
      DifferentiableAt ℝ (fun x => modes F l x i j) z :=
    (SmoothCoefficient.smooth_mode hF hz l i j).differentiableAt (by decide)
  rw [offDiagonal_congr (b := fun x => modes U l x + modes V l x) hz (fun _ hy => modes_add hu hv hy l)
    (hD hUV) (fun i j => (hD hu i j).add (hD hv i j))]
  simp only [offDiagonal, attenuation_add]
  ext i j
  simp only [geodesicTerm, Matrix.add_apply, fderiv_fun_add (hD hu i j) (hD hv i j),
    ContinuousLinearMap.add_apply]
  ring

/-- The correction in Proposition 3.1 for genuine chart fields. An
unrestricted solution U and homogeneous solution V yield a holomorphic
solution by taking the nonnegative part of their sum. Only the two stated
first-order conditions on the low modes of V have to be imposed. -/
theorem corrected_solves {lam : ℂ → ℝ} {A U V P : Field n} {t s : ℝ}
    (ha : SmoothToBoundary A) (hu : SmoothToBoundary U) (hv : SmoothToBoundary V)
    (hp : SmoothToBoundary P) (hm : ThreeModes A) (hU : Solves lam A U t s)
    (hV : ∀ z ∈ closedBall (0 : ℂ) 1, ∀ k : ℤ, transport lam A t s (modes V) k z = 0)
    (lower : ∀ z ∈ closedBall (0 : ℂ) 1,
      offDiagonal lam A t s (-1) 0 (modes V 0) z =
        offDiagonal lam A t s 1 (-2) (modes U (-2)) z + attenuationTerm A t s 0 (modes U (-1) z) z)
    (raise : ∀ z ∈ closedBall (0 : ℂ) 1,
      offDiagonal lam A t s 1 (-1) (modes V (-1)) z = -offDiagonal lam A t s 1 (-1) (modes U (-1)) z)
    (proj : ∀ z ∈ closedBall (0 : ℂ) 1, ∀ k : ℤ,
      modes P k z = if 0 ≤ k then modes U k z + modes V k z else 0) :
    ModesFrom 0 P ∧ Solves lam A P t s := by
  have hUV : SmoothToBoundary (U+V) := fun x hx θ i j => (hu x hx θ i j).add (hv x hx θ i j)
  have hsum : Solves lam A (U+V) t s := by
    apply (solves_iff_neighbors t s ha hUV hm).mpr
    intro z hz k
    rw [← (solves_iff_neighbors t s ha hu hm).mp hU z hz k, ← add_zero (transport _ _ _ _ (modes U) k z),
      ← hV z hz k]
    simp only [transport, offDiagonal_add hu hv _ _ _ _ _ _ hz, modes_add hu hv hz, attenuation_add]
    abel
  constructor
  · intro z hz i j k hk
    have h := congrArg (fun M : Mat n => M i j) (proj z hz k)
    simpa only [if_neg (not_le.mpr hk), Matrix.zero_apply] using h
  · apply (projected_solves_iff_two_defects ha hUV hp hm hsum (fun z hz k =>
      (proj z hz k).trans (by rw [modes_add hu hv hz]))).mpr
    intro z hz
    have h := hV z hz (-1)
    norm_num only [transport, Int.reduceSub, Int.reduceNeg, Int.reduceAdd] at h
    rw [lower z hz] at h
    simp only [offDiagonal_add hu hv _ _ _ _ _ _ hz, modes_add hu hv hz, attenuation_add, raise z hz,
      add_neg_cancel, and_true]
    linear_combination (norm := abel) h

end TransportOkaGrauert.ModeTransport
