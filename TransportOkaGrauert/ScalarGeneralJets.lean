import TransportOkaGrauert.ScalarGeneral
import TransportOkaGrauert.ScalarGeneralModes

/-! Finite-order scalar transport inversion at the zero section for arbitrary
smooth conformal disks. Each step removes one further angular mode by an
explicit one-mode primitive, and preserves a smooth disk representative for
the whole remaining tail. -/
noncomputable section
namespace TransportOkaGrauert.ScalarGeneralJets
open Complex Metric ChartCorrespondence PencilLifts ScalarGeneral ScalarGeneralModes Isothermal
open scoped ContDiff

def monomial (k : ℕ) (a : ℂ → ℂ) (ha : ContDiff ℝ ∞ a) : DiskFunction where
  val p := a p.1 * p.2 ^ k
  smooth := (ha.comp contDiff_fst).mul (contDiff_snd.pow k)
  fibre z _ := (differentiableOn_const (a z)).mul (differentiableOn_id.pow k)

theorem raising_smooth {σ : ℂ → ℝ} (hs : ContDiff ℝ ∞ σ)
    {u : ℂ → ℂ} (hu : ContDiff ℝ ∞ u) (k : ℤ) : ContDiff ℝ ∞ (fun z => raising σ u z k) := by
  let df := hu.fderiv_right (m := ∞) (by simp)
  let ds := hs.fderiv_right (m := ∞) (by simp)
  apply (Complex.ofRealCLM.contDiff.comp hs.neg.exp).mul
  apply ContDiff.add
  · exact ((df.clm_apply contDiff_const).div_const 2).add ((df.clm_apply contDiff_const).div_const _)
  · exact ((((Complex.ofRealCLM.contDiff.comp (ds.clm_apply contDiff_const)).div_const _).sub
      ((Complex.ofRealCLM.contDiff.comp (ds.clm_apply contDiff_const)).div_const _)).mul hu).mul contDiff_const

theorem transport_monomial {σ : ℂ → ℝ} {u : ℂ → ℂ} (hu : ContDiff ℝ ∞ u)
    (k : ℕ) (z : ℂ) (w : Circle) :
    boundaryTransport σ (monomial (k+1) u hu).val z w = (Real.exp (σ z) : ℂ) *
      (raising σ u z (k+1) * (w:ℂ)^(k+2) + lowering σ u z (k+1) * (w:ℂ)^k) := by
  let f := monomial (k+1) u hu
  have he := geodesicX_mode σ u z (hu.differentiable (by simp) z) ((k:ℤ)+1) w
  have trace := geodesicX_trace f.smooth σ z w
  have ident : (fun p (v:Circle) => f.val (p,(v:ℂ))) = fun p v => u p * Fourier.character ((k:ℤ)+1) v := by
    funext p v
    simp [f,monomial,Fourier.character,zpow_add₀,pow_succ]
  rw [ident, he] at trace
  have hp : (Real.exp (σ z) : ℂ) * (Real.exp (-σ z) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, Complex.ofReal_one]
  change boundaryTransport σ f.val z w = _
  have hpow : Fourier.character ((k:ℤ)+1+1) w = (w:ℂ)^(k+2) := by
    change (w:ℂ)^((k:ℤ)+1+1) = _
    norm_cast
  have hlow : Fourier.character ((k:ℤ)+1+ -1) w = (w:ℂ)^k := by simp [Fourier.character]
  rw [hpow, hlow] at trace
  rw [trace, ← mul_assoc, hp, one_mul]

/-- Remove the leading coefficient of `w^k r` without creating any lower
frequencies. The primitive is a monomial of degree `k+1`. -/
theorem lift_leading_mode {σ : ℂ → ℝ} (hs : ContDiff ℝ ∞ σ) (k : ℕ) (r : DiskFunction) :
    ∃ b g : DiskFunction, ∀ z ∈ disk, ∀ w : Circle, (w:ℂ)^k * r.val (z,w) =
      boundaryTransport σ b.val z w + (w:ℂ)^(k+1) * g.val (z,w) := by
  obtain ⟨g,hg⟩ := divide_at_zero r
  obtain ⟨u,hu,heq⟩ := lowering_surjective hs ((k:ℤ)+1)
    (fun z => (Real.exp (-σ z) : ℂ) * r.val (z,0))
    ((Complex.ofRealCLM.contDiff.comp hs.neg.exp).mul (r.smooth.comp (contDiff_id.prodMk contDiff_const)))
  let a (z : ℂ) := (Real.exp (σ z) : ℂ) * raising σ u z ((k:ℤ)+1)
  have ha : ContDiff ℝ ∞ a := (Complex.ofRealCLM.contDiff.comp hs.exp).mul (raising_smooth hs hu _)
  refine ⟨monomial (k+1) u hu, g.sub (monomial 1 a ha), ?_⟩
  intro z hz w
  change _ = boundaryTransport σ (monomial (k+1) u hu).val z w + (w:ℂ)^(k+1) * (g.val (z,w) - a z * (w:ℂ)^1)
  rw [transport_monomial hu, heq z (ball_subset_closedBall hz)]
  have hq := hg z hz (w:ℂ) (sphere_subset_closedBall w.property)
  have hp : (Real.exp (σ z) : ℂ) * (Real.exp (-σ z) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, Complex.ofReal_one]
  dsimp [a]
  simp only [pow_succ, mul_add]
  linear_combination (norm := ring) -(w:ℂ)^k * hq - (w:ℂ)^k * r.val (z,0) * hp

/-- An actual smooth approximate primitive to every order, for the exact
`ShiftExtends` sources used by the pencils. The trace of the residual is
`w^N` times a jointly smooth fibre-holomorphic disk function. -/
theorem solve_through_modes {σ : ℂ → ℝ} (hs : ContDiff ℝ ∞ σ) {rhs : TraceRHS} (h : ShiftExtends rhs) (N : ℕ) :
    ∃ u g : DiskFunction, ∀ z ∈ disk, ∀ w : Circle,
      rhs z w = boundaryTransport σ u.val z w + (w:ℂ)^N * g.val (z,w) := by
  induction N with
  | zero => simpa using split_source h σ
  | succ n ih =>
    obtain ⟨u,r,hu⟩ := ih
    obtain ⟨b,g,hb⟩ := lift_leading_mode hs n r
    let v : DiskFunction := ⟨fun p => u.val p + b.val p, u.smooth.add b.smooth,
      fun z hz => (u.fibre z hz).add (b.fibre z hz)⟩
    refine ⟨v,g,?_⟩
    intro z hz w
    have hv : boundaryTransport σ v.val z w = boundaryTransport σ u.val z w + boundaryTransport σ b.val z w :=
      congrArg (fun L : ChartStein.E →L[ℝ] ℂ => L ((w:ℂ), (Isothermal.angularDrift σ z w : ℂ)*(I*w)))
        (((u.smooth.differentiable (by simp) (z,(w:ℂ))).hasFDerivAt.add
          (b.smooth.differentiable (by simp) (z,(w:ℂ))).hasFDerivAt).fderiv)
    rw [hu z hz, hb z hz, hv, add_assoc]

/-- For every prescribed cutoff `N`, the full pencil solver is equivalent to
solvability just on the tails `w^N g`. No uniformity as `N` increases is used. -/
theorem scalarSolvability_iff_tail {σ : ℂ → ℝ} (hs : ContDiff ℝ ∞ σ) (N : ℕ) :
    ScalarSolvability σ ↔ ∀ g : DiskFunction, ∃ v : DiskFunction, ∀ z ∈ disk, ∀ w : Circle,
      boundaryTransport σ v.val z w = (w:ℂ)^N * g.val (z,w) := by
  constructor
  · intro solve g
    let p := (monomial N (fun _ => 1) contDiff_const).mul g
    simpa [p, monomial, DiskFunction.mul] using solve _ (shifted_disk_function p)
  · intro solve rhs h
    obtain ⟨u,g,hu⟩ := solve_through_modes hs h N
    obtain ⟨v,hv⟩ := solve g
    let f : DiskFunction := ⟨fun p => u.val p + v.val p, u.smooth.add v.smooth,
      fun z hz => (u.fibre z hz).add (v.fibre z hz)⟩
    refine ⟨f, ?_⟩
    intro z hz w
    rw [hu z hz, ← hv z hz]
    exact congrArg (fun L : ChartStein.E →L[ℝ] ℂ => L ((w:ℂ), (angularDrift σ z w : ℂ)*(I*w)))
      (((u.smooth.differentiable (by simp) (z,(w:ℂ))).hasFDerivAt.add
        (v.smooth.differentiable (by simp) (z,(w:ℂ))).hasFDerivAt).fderiv)

end TransportOkaGrauert.ScalarGeneralJets
