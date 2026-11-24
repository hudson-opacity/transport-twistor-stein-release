import TransportOkaGrauert.NearDiagonal

/-! A single gauge normalization to a skew-Hermitian pair before the ray
continuation argument. Frequencies, adjoints and the rank-squared action
are computed on the actual disk chart. -/

noncomputable section
namespace TransportOkaGrauert.SkewReduction

open SimpleDiskTarget ChartOrbits ChartModes Metric Complex Real MeasureTheory
open scoped ComplexConjugate ContDiff
local instance : Fact (0 < 2 * π) := ⟨Real.two_pi_pos⟩

/-- Conjugate transposition is the adjoint on the finite-dimensional
Hermitian space (or on the matrix units indexed by pairs). -/
def SkewOnDisk {ι : Type*} (B : ℂ → Circle → Matrix ι ι ℂ) : Prop :=
  ∀ z ∈ closedBall (0 : ℂ) 1, ∀ v : Circle, (B z v).conjTranspose = -(B z v)

def ThreeModes {ι : Type*} (B : ℂ → Circle → Matrix ι ι ℂ) : Prop :=
  ∀ z ∈ closedBall (0 : ℂ) 1, ∀ (i j : ι) (k : ℤ), k < -1 ∨ 1 < k →
    fourierCoeff (fun θ : DiskSeries.Angle => B z θ.toCircle i j) k = 0

/-- Complex conjugation reverses the Fourier frequency. -/
theorem coeff_conj (f : DiskSeries.Angle → ℂ) (k : ℤ) :
    fourierCoeff (fun θ => conj (f θ)) k = conj (fourierCoeff f (-k)) := by
  simp only [fourierCoeff, smul_eq_mul, neg_neg, ← integral_conj, map_mul, ← fourier_neg]

private theorem coeff_neg (f : DiskSeries.Angle → ℂ) (k : ℤ) :
    fourierCoeff (fun θ => -f θ) k = -fourierCoeff f k := by
  simp only [fourierCoeff, smul_eq_mul, mul_neg, integral_neg]

/-- The mode at k is minus the coefficientwise adjoint at −k. -/
theorem skew_coeff {ι : Type*} {B : ℂ → Circle → Matrix ι ι ℂ} (h : SkewOnDisk B)
    (z : ℂ) (hz : z ∈ closedBall 0 1) (i j : ι) (k : ℤ) :
    fourierCoeff (fun θ : DiskSeries.Angle => B z θ.toCircle i j) k =
      -conj (fourierCoeff (fun θ : DiskSeries.Angle => B z θ.toCircle j i) (-k)) := by
  have he : (fun θ : DiskSeries.Angle => B z θ.toCircle i j) =
      fun θ => -conj (B z θ.toCircle j i) := by
    funext θ
    have hv := congrArg (fun M : Matrix ι ι ℂ => M i j) (h z hz θ.toCircle)
    change conj (B z θ.toCircle j i) = -(B z θ.toCircle i j) at hv
    rw [hv, neg_neg]
  rw [he, coeff_neg, coeff_conj]

variable {n : ℕ}

/-- Skew-Hermitian symmetry and the lower cutoff leave only −1, 0, and 1. -/
theorem skew_threeModes {B : Field n} (hm : ModesFrom (-1) B) (h : SkewOnDisk B) : ThreeModes B := by
  rintro z hz i j k (hl | hr)
  · exact hm z hz i j k hl
  · rw [skew_coeff h z hz i j k, hm z hz j i (-k) (by omega), map_zero, neg_zero]

/-- Matrix on the n² matrix units for the mixed attenuation.
The transpose in the right multiplication term follows from the order
of the two column indices. -/
def mixed {ι : Type*} [DecidableEq ι] (B : Matrix ι ι ℂ) (t s : ℝ) :
    Matrix (ι × ι) (ι × ι) ℂ := fun a b =>
  (if b.2 = a.2 then (t : ℂ) * B a.1 b.1 else 0) -
  (if b.1 = a.1 then (s : ℂ) * B b.2 a.2 else 0)

/-- In coordinates this matrix acts by t B U − s U B. -/
theorem mixed_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι] (B U : Matrix ι ι ℂ)
    (t s : ℝ) (i j : ι) :
    ((mixed B t s).mulVec (fun p => U p.1 p.2)) (i,j) =
      ((t • B) * U - U * (s • B)) i j := by
  simp only [Matrix.mulVec, dotProduct, mixed, sub_mul, Finset.sum_sub_distrib,
    Fintype.sum_prod_type, Matrix.sub_apply, Matrix.mul_apply, Matrix.smul_apply, Complex.real_smul]
  congr 1
  · simp [ite_mul]
  · rw [Finset.sum_comm]
    simp [mul_comm]

/-- Real amplitudes preserve skew-Hermitian symmetry in the entire
mixed rank-squared attenuation, including unequal amplitudes. -/
theorem mixed_skew {ι : Type*} [DecidableEq ι] (B : Matrix ι ι ℂ) (h : B.conjTranspose = -B)
    (t s : ℝ) : (mixed B t s).conjTranspose = -(mixed B t s) := by
  have hj (i j : ι) : conj (B j i) = -B i j :=
    congrArg (fun M : Matrix ι ι ℂ => M i j) h
  ext ⟨i,j⟩ ⟨p,q⟩
  by_cases hip : i = p <;> by_cases hjq : j = q <;>
    (simp [Matrix.conjTranspose_apply, mixed, hip, hjq, Ne.symm, eq_comm, hj, RCLike.star_def, mul_neg]; try ring)

theorem entry_continuous {B : Field n} (hs : SmoothToBoundary B) (z : ℂ)
    (hz : z ∈ closedBall 0 1) (i j : Fin n) :
    Continuous (fun θ : DiskSeries.Angle => B z θ.toCircle i j) := by
  apply continuous_coinduced_dom.mpr
  change Continuous (fun t : ℝ => B z (AddCircle.toCircle (t : DiskSeries.Angle)) i j)
  simpa only [ChartModes.toCircle_angle] using
    (ChartModes.slice_smooth hs hz i j).continuous

/-- Coefficient matrices of the angular field. -/
def modeMatrix {ι : Type*} (B : ℂ → Circle → Matrix ι ι ℂ) (z : ℂ) (k : ℤ) :
    Matrix ι ι ℂ :=
  fun i j => fourierCoeff (fun θ : DiskSeries.Angle => B z θ.toCircle i j) k

/-- A continuous three-mode chart field is pointwise its finite Laurent
polynomial on the entire velocity circle. -/
theorem threeMode_expansion {B : Field n} (hs : SmoothToBoundary B) (hm : ThreeModes B)
    (z : ℂ) (hz : z ∈ closedBall 0 1) (v : Circle) :
    B z v = conj (v : ℂ) • modeMatrix B z (-1) + modeMatrix B z 0 +
      (v : ℂ) • modeMatrix B z 1 := by
  let θ : DiskSeries.Angle := (arg (v : ℂ) : ℝ)
  have hθ : θ.toCircle = v := (ChartModes.toCircle_angle _).trans (Circle.exp_arg v)
  ext i j
  let a : C(DiskSeries.Angle, ℂ) := ⟨fun x => B z x.toCircle i j, entry_continuous hs z hz i j⟩
  let S : Finset ℤ := {-1, 0, 1}
  have hzero (k : ℤ) (hk : k ∉ S) : fourierCoeff a k = 0 := by
    apply hm z hz i j k
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hk
    omega
  have hsum : Summable (fourierCoeff a) := (hasSum_sum_of_ne_finset_zero hzero).summable
  have hfour := has_pointwise_sum_fourier_series_of_summable hsum θ
  have hpoly : HasSum (fun k : ℤ => fourierCoeff a k • fourier k θ)
      (∑ k ∈ S, fourierCoeff a k • fourier k θ) :=
    hasSum_sum_of_ne_finset_zero (fun k hk => by simp [hzero k hk])
  have he := hfour.unique hpoly
  change B z θ.toCircle i j = _ at he
  rw [hθ] at he
  simp only [S, Finset.sum_insert (by decide : (-1 : ℤ) ∉ ({0,1} : Finset ℤ)),
    Finset.sum_insert (by decide : (0 : ℤ) ∉ ({1} : Finset ℤ)), Finset.sum_singleton,
    fourier_zero, fourier_neg (n := 1), fourier_one, hθ, smul_eq_mul, mul_one] at he
  change B z v i j = conj (v : ℂ) * fourierCoeff a (-1) + fourierCoeff a 0 +
    (v : ℂ) * fourierCoeff a 1
  rw [he]
  ring

/-- The coefficients satisfy the `u(n)` connection/Higgs pairing. -/
theorem modeMatrix_adjoint {ι : Type*} {B : ℂ → Circle → Matrix ι ι ℂ} (h : SkewOnDisk B)
    (z : ℂ) (hz : z ∈ closedBall 0 1) (k : ℤ) :
    (modeMatrix B z (-k)).conjTranspose = -modeMatrix B z k := by
  ext i j
  change conj (fourierCoeff _ (-k)) = -(fourierCoeff _ k)
  rw [skew_coeff h z hz i j k, neg_neg]

private theorem scaled_sub_coeff (f g : DiskSeries.Angle → ℂ) (hf : Continuous f) (hg : Continuous g)
    (t s : ℂ) (k : ℤ) : fourierCoeff (fun θ => t * f θ - s * g θ) k =
      t * fourierCoeff f k - s * fourierCoeff g k := by
  let u := fun θ => t * f θ
  let v := fun θ => -(s * g θ)
  have hu : Integrable u AddCircle.haarAddCircle :=
    (continuous_const.mul hf).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hv : Integrable v AddCircle.haarAddCircle :=
    (continuous_const.mul hg).neg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  change fourierCoeff (u + v) k = _
  rw [fourierCoeff.add hu hv, Pi.add_apply]
  simp only [u, v, coeff_neg, fourierCoeff.const_mul, sub_eq_add_neg]

theorem mixed_threeModes {B : Field n} (hs : SmoothToBoundary B) (hm : ThreeModes B)
    (t s : ℝ) : ThreeModes (fun z v => mixed (B z v) t s) := by
  rintro z hz ⟨i,j⟩ ⟨p,q⟩ k hk
  have h := scaled_sub_coeff (fun θ : DiskSeries.Angle => B z θ.toCircle i p)
    (fun θ : DiskSeries.Angle => B z θ.toCircle q j)
    (entry_continuous hs z hz i p) (entry_continuous hs z hz q j)
    (if q = j then (t : ℂ) else 0) (if p = i then (s : ℂ) else 0) k
  rw [hm z hz i p k hk, hm z hz q j k hk, mul_zero, mul_zero, sub_zero] at h
  by_cases hq : q = j <;> by_cases hp : p = i <;> simpa [mixed, hq, hp] using h

/-- Passing to the n² coordinates preserves smoothness up to the base
boundary for the full mixed attenuation. -/
theorem mixed_smooth {B : Field n} (hs : SmoothToBoundary B) (t s : ℝ)
    (z : ℂ) (hz : z ∈ closedBall 0 1) (θ : ℝ) (a b : Fin n × Fin n) :
    ContDiffAt ℝ ∞ (fun p : ℂ × ℝ => mixed (B p.1 (Circle.exp p.2)) t s a b) (z, θ) := by
  have h₁ := (hs z hz θ a.1 b.1).const_smul (if b.2 = a.2 then (t : ℂ) else 0)
  have h₂ := (hs z hz θ b.2 a.2).const_smul (if b.1 = a.1 then (s : ℂ) else 0)
  by_cases hc : b.2 = a.2 <;> by_cases hr : b.1 = a.1 <;>
    simpa [mixed, hc, hr, smul_eq_mul] using h₁.sub h₂

/-- The mixed operator is one skew-Hermitian connection/Higgs-mode pair
at each real amplitude pair (t,s). -/
theorem mixed_pair {B : Field n} (hs : SmoothToBoundary B) (hm : ModesFrom (-1) B)
    (h : SkewOnDisk B) (t s : ℝ) :
    SkewOnDisk (fun z v => mixed (B z v) t s) ∧ ThreeModes (fun z v => mixed (B z v) t s) :=
  ⟨fun z hz v => mixed_skew _ (h z hz v) t s, mixed_threeModes hs (skew_threeModes hm h) t s⟩

/-- A frame for the one normalized attenuation gives a frame for the
original attenuation by composition. -/
theorem transport_back {lam : ℂ → ℝ} {A B F G J K : Field n}
    (h : RelativeFrame lam A B F G) (hB : IsFrame lam B J K) :
    IsFrame lam A (F * J) (K * G) := by
  have r : RelativeFrame lam B 0 J K := by
    refine ⟨hB.smoothF, hB.smoothG, hB.modesF, hB.modesG, hB.inverses, ?_⟩
    intro z hz v
    ext i j
    simpa [chartX] using hB.transport z hz v i j
  exact (h.trans r).toFrame

/-- Reduction with a single gauge change per attenuation, followed by scalar
ray continuation applied to the fixed normalized pair. -/
theorem chartTarget_of_skew_mixed
    (normalize : ∀ lam, SimpleMetric lam → ∀ (n : ℕ) (A : SimpleDiskTarget.Field n), SmoothToBoundary A → ModesFrom (-1) A →
      ∃ B F G, SmoothToBoundary B ∧ ModesFrom (-1) B ∧ SkewOnDisk B ∧ RelativeFrame lam A B F G)
    (solve : ∀ lam, SimpleMetric lam → ∀ (n : ℕ) (B : SimpleDiskTarget.Field n), SmoothToBoundary B →
      SkewOnDisk B → ThreeModes B → NearDiagonal.BoundedMixedSolvability lam B) :
    chartIntegratingFactorTarget := by
  intro lam hsimple n A hs hm
  obtain ⟨B, F, G, hsB, hmB, hskew, hrel⟩ := normalize lam hsimple n A hs hm
  obtain ⟨J, K, hB⟩ := NearDiagonal.frame_of_bounded_mixed_solutions
    (solve lam hsimple n B hsB hskew (skew_threeModes hmB hskew))
  exact ⟨_, _, transport_back hrel hB⟩

end TransportOkaGrauert.SkewReduction
