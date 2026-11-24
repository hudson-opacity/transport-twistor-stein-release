import TransportOkaGrauert.SkewReduction
import TransportOkaGrauert.ShiftedModes
import TransportOkaGrauert.ChartRegularity
import TransportOkaGrauert.ChartCoefficients

/-! Skew normalization of an admissible attenuation by an ordinary transport
frame factored into a holomorphic gauge and a pointwise unitary field.
All identities are on the prescribed closed disk. -/

noncomputable section
namespace TransportOkaGrauert.LoopNormalization
open SimpleDiskTarget ChartOrbits ChartModes SkewReduction Metric MeasureTheory
open scoped ComplexConjugate ContDiff
local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩
variable {n : ℕ}

/-- The adjoint of a boundary field, pointwise on the unit velocity circle. -/
def adj (F : Field n) : Field n := fun z v => (F z v).conjTranspose

theorem smooth_adj {F : Field n} (hf : SmoothToBoundary F) : SmoothToBoundary (adj F) := by
  intro z hz θ i j
  exact Complex.conjCLE.contDiff.contDiffAt.comp _ (hf z hz θ j i)

theorem chartX_adj {F : Field n} (lam : ℂ → ℝ) (hf : SmoothToBoundary F)
    {z : ℂ} (hz : z ∈ closedBall 0 1) (v : Circle) :
    chartX lam (adj F) z v = (chartX lam F z v).conjTranspose := by
  obtain ⟨θ, rfl⟩ : ∃ θ, Circle.exp θ = v := ⟨_, Circle.exp_arg v⟩
  ext i j
  have hd := (hf z hz θ j i).differentiableAt (by decide)
  have hc := Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp (z,θ) hd.hasFDerivAt
  change Isothermal.geodesicX lam (fun p w => adj F p w i j) z (Circle.exp θ) =
    conj (Isothermal.geodesicX lam (fun p w => F p w j i) z (Circle.exp θ))
  rw [PathContinuation.geodesicX_eq_chart_derivative _ _ _ _ (hc.differentiableAt),
    PathContinuation.geodesicX_eq_chart_derivative _ _ _ _ hd]
  exact congrArg (fun L : (ℂ × ℝ) →L[ℝ] ℂ => L (PathContinuation.chartVector lam (z,θ))) hc.fderiv

private theorem modes_add {m : ℤ} {F G : Field n} (hf : SmoothToBoundary F)
    (hg : SmoothToBoundary G) (mf : ModesFrom m F) (mg : ModesFrom m G) :
    ModesFrom m (F+G) := by
  intro z hz i j k hk
  let f := fun θ : DiskSeries.Angle => F z θ.toCircle i j
  let g := fun θ : DiskSeries.Angle => G z θ.toCircle i j
  have hfi : Integrable f AddCircle.haarAddCircle := (entry_continuous hf z hz i j).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hgi : Integrable g AddCircle.haarAddCircle := (entry_continuous hg z hz i j).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  change fourierCoeff (f+g) k = 0
  rw [fourierCoeff.add hfi hgi, Pi.add_apply, mf z hz i j k hk, mg z hz i j k hk, add_zero]

/-- Smooth holomorphic factors H, G inverse to one another, and a smooth
pointwise unitary factor V on the real velocity circle. -/
structure GaugeFactors (H G V : Field n) : Prop where
  smoothH : SmoothToBoundary H
  smoothG : SmoothToBoundary G
  smoothV : SmoothToBoundary V
  modesH : ModesFrom 0 H
  modesG : ModesFrom 0 G
  inverses : ∀ z ∈ closedBall (0 : ℂ) 1, ∀ v, H z v * G z v = 1 ∧ G z v * H z v = 1
  unitary : ∀ z ∈ closedBall (0 : ℂ) 1, ∀ v, V z v * (V z v).conjTranspose = 1

/-- The product of the factors solves ordinary transport. -/
structure FactoredFrame (lam : ℂ → ℝ) (A H G V : Field n) : Prop extends GaugeFactors H G V where
  transport : ∀ z ∈ closedBall (0 : ℂ) 1, ∀ v,
    chartX lam (H*V) z v + A z v * (H*V) z v = 0

def normalized (lam : ℂ → ℝ) (A H G : Field n) := G * (chartX lam H + A * H)

variable {lam : ℂ → ℝ} {A H G V : Field n}

theorem FactoredFrame.relative (h : FactoredFrame lam A H G V) :
    RelativeFrame lam A (normalized lam A H G) H G := by
  refine ⟨h.smoothH, h.smoothG, h.modesH, h.modesG, h.inverses, ?_⟩
  intro z hz v
  simp only [normalized, Pi.mul_apply, Pi.add_apply, ← mul_assoc, (h.inverses z hz v).1, one_mul]

/-- Differentiate the unitary identity and the ordinary transport equation
to recover the skew-Hermitian normalized field pointwise. -/
theorem FactoredFrame.skew (h : FactoredFrame lam A H G V) :
    SkewOnDisk (normalized lam A H G) := by
  intro z hz v
  let B := normalized lam A H G z v
  let U := V z v
  let D := chartX lam V z v
  have rel := h.relative.transport z hz v
  have hx := h.transport z hz v
  rw [chartX_mul _ h.smoothH h.smoothV hz v] at hx
  have hG := (h.inverses z hz v).2
  have hu : U * U.conjTranspose = 1 := h.unitary z hz v
  have hx' : H z v * (B*U + D) = 0 := by
    calc
      _ = (H z v * B)*U + H z v * D := by noncomm_ring
      _ = chartX lam H z v * V z v + H z v * chartX lam V z v + A z v * (H z v * V z v) := by
        rw [← rel]; dsimp only [U, D]; noncomm_ring
      _ = 0 := hx
  have hBD : B*U + D = 0 := by
    simpa only [← mul_assoc, hG, one_mul, mul_zero] using congrArg (G z v * ·) hx'
  have hb : B = -(D * U.conjTranspose) := by
    have hval := congrArg (· * U.conjTranspose) hBD
    simp only [add_mul, mul_assoc B U, hu, mul_one, zero_mul] at hval
    exact eq_neg_of_add_eq_zero_left hval
  have hconst := chartX_eq (lam := lam) (G := (1 : Field n)) (smooth_mul h.smoothV (smooth_adj h.smoothV))
    (fun _ _ _ _ _ => contDiffAt_const : SmoothToBoundary (1 : Field n))
    (fun p hp w => h.unitary p hp w) hz v
  rw [chartX_mul _ h.smoothV (smooth_adj h.smoothV) hz v, chartX_one, chartX_adj _ h.smoothV hz v] at hconst
  change D * U.conjTranspose + U * D.conjTranspose = 0 at hconst
  change B.conjTranspose = -B
  rw [hb, Matrix.conjTranspose_neg, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, neg_neg]
  exact (eq_neg_of_add_eq_zero_left hconst).symm

theorem FactoredFrame.normalize (h : FactoredFrame lam A H G V)
    (hs : SmoothToBoundary A) (hm : ModesFrom (-1) A)
    (hlam : ∀ z ∈ closedBall (0 : ℂ) 1, ContDiffAt ℝ ∞ lam z) :
    SmoothToBoundary (normalized lam A H G) ∧ ModesFrom (-1) (normalized lam A H G) ∧
      SkewOnDisk (normalized lam A H G) ∧ RelativeFrame lam A (normalized lam A H G) H G := by
  have hX := ChartRegularity.smooth_chartX hlam h.smoothH
  have mX : ModesFrom (-1) (chartX lam H) := ChartCoefficients.chartX_modes lam h.smoothH h.modesH
  have ha := smooth_mul hs h.smoothH
  have hsum : SmoothToBoundary (chartX lam H + A*H) := fun z hz θ i j =>
    (hX z hz θ i j).add (ha z hz θ i j)
  exact ⟨smooth_mul h.smoothG hsum, ShiftedModes.mul_left h.smoothG hsum h.modesG
    (modes_add hX ha mX (ShiftedModes.mul_right hs h.smoothH hm h.modesH)), h.skew, h.relative⟩

/-- General simple conformal disk theorem reduced to the published
ordinary transport/loop factorization and the locally bounded linear
endpoint correction for skew-Hermitian three-mode coefficients. -/
theorem chartTarget_of_factorization_and_estimate
    (factor : ∀ lam, SimpleMetric lam → ∀ (n : ℕ) (A : SimpleDiskTarget.Field n),
      SmoothToBoundary A → ModesFrom (-1) A → ∃ H G V, FactoredFrame lam A H G V)
    (estimate : ∀ lam, SimpleMetric lam → ∀ (n : ℕ) (B : SimpleDiskTarget.Field n),
      SmoothToBoundary B → SkewOnDisk B → ThreeModes B →
        NearDiagonal.BoundedMixedSolvability lam B) :
    chartIntegratingFactorTarget := by
  apply chartTarget_of_skew_mixed _ estimate
  intro lam hsimple n A hs hm
  obtain ⟨H, G, V, h⟩ := factor lam hsimple n A hs hm
  exact ⟨_, H, G, h.normalize hs hm (fun _ _ => hsimple.smooth.contDiffAt)⟩

/-- A loop factorization of a given smooth invertible field, independent
of the metric and of any transport equation. -/
structure LoopFactors (R H G V : Field n) : Prop extends GaugeFactors H G V where
  product : ∀ z ∈ closedBall (0 : ℂ) 1, ∀ v, H z v * V z v = R z v

/-- The ordinary equation can be differentiated through the factorization
even when its equality with R is known only on the closed base disk. -/
theorem LoopFactors.of_ordinary {R : Field n} (h : LoopFactors R H G V)
    (hs : SmoothToBoundary R)
    (he : ∀ z ∈ closedBall (0 : ℂ) 1, ∀ v, chartX lam R z v + A z v * R z v = 0) :
    FactoredFrame lam A H G V := by
  refine ⟨h.toGaugeFactors, ?_⟩
  intro z hz v
  have hx := chartX_eq (lam := lam) (F := H*V) (G := R)
    (smooth_mul h.smoothH h.smoothV) hs h.product hz v
  simpa only [hx, Pi.mul_apply, h.product z hz v] using
    (he z hz v : chartX lam R z v + A z v * R z v = 0)

/-- The three independent geometric and analytic inputs in the manuscript.
Only the last concerns holomorphic solutions of an inhomogeneous transport
equation, and it is restricted to skew-Hermitian three-mode pairs. -/
theorem chartTarget_of_three_inputs
    (ordinary : ∀ lam, SimpleMetric lam → ∀ (n : ℕ) (A : SimpleDiskTarget.Field n),
      SmoothToBoundary A → ∃ R, SmoothToBoundary R ∧
      (∀ z ∈ closedBall (0 : ℂ) 1, ∀ v, IsUnit (R z v)) ∧
      ∀ z ∈ closedBall (0 : ℂ) 1, ∀ v, chartX lam R z v + A z v * R z v = 0)
    (iwasawa : ∀ (n : ℕ) (R : SimpleDiskTarget.Field n), SmoothToBoundary R →
      (∀ z ∈ closedBall (0 : ℂ) 1, ∀ v, IsUnit (R z v)) → ∃ H G V, LoopFactors R H G V)
    (estimate : ∀ lam, SimpleMetric lam → ∀ (n : ℕ) (B : SimpleDiskTarget.Field n),
      SmoothToBoundary B → SkewOnDisk B → ThreeModes B →
        NearDiagonal.BoundedMixedSolvability lam B) :
    chartIntegratingFactorTarget := by
  apply chartTarget_of_factorization_and_estimate _ estimate
  intro lam hsimple n A hs _
  obtain ⟨R,hR,inv,he⟩ := ordinary lam hsimple n A hs
  obtain ⟨H,G,V,h⟩ := iwasawa n R hR inv
  exact ⟨H,G,V,h.of_ordinary hR he⟩

end TransportOkaGrauert.LoopNormalization
