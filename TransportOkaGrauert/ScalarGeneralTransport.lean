import TransportOkaGrauert.ScalarGeneralUnrestricted

/-! Smooth unrestricted scalar transport on every simple disk, including its
boundary, with descent from real lifted angles to the velocity circle. -/
noncomputable section
namespace TransportOkaGrauert.ScalarGeneralTransport
open Complex Set Metric SimpleDiskTarget PathContinuation ScalarGeneralFlow GeodesicFlowExtension ScalarGeneralUnrestricted
open scoped ContDiff

abbrev Trace := ℂ → Circle → ℂ
def lifted (f : Trace) (p : State) : ℂ := f p.1 (Circle.exp p.2)
private def shift (c : ℝ) (p : State) := p + (0,c)

private theorem flow_shift {σ : ℂ → ℝ} (hs : ContDiff ℝ ∞ σ) (Φ : SmoothFlow State)
    (D : ∀ p t, HasDerivAt (fun s => Φ.val (p,s)) (extended σ (Φ.val (p,t))) t)
    {c : ℝ} (hc : Circle.exp c = 1) (p : State) (t : ℝ) : Φ.val (shift c p,t) = shift c (Φ.val (p,t)) := by
  obtain ⟨B,lip,_⟩ := bounded_lipschitz hs
  have inv (q : State) : extended σ (shift c q) = extended σ q := by
    simp [extended, chartVector, shift, Circle.exp_add, hc]
  have d (s : ℝ) : HasDerivAt (fun r => shift c (Φ.val (p,r))) (extended σ (shift c (Φ.val (p,s)))) s := by
    rw [inv]; exact (D p s).add_const _
  have eq := ODE_solution_unique_univ (v := fun _ => extended σ) (s := fun _ => univ)
    (fun _ => lip.lipschitzOnWith) (fun s => ⟨D (shift c p) s,trivial⟩) (fun s => ⟨d s,trivial⟩)
    (t₀ := 0) (by simp [Φ.initial])
  exact congrFun eq t

/-- Every globally smooth angular source on a simple conformal disk has a
globally smooth circle-valued-velocity representative of a complex primitive.
The equation holds also on the base boundary. -/
theorem smooth_primitive {σ : ℂ → ℝ} (simple : SimpleMetric σ) (f : Trace) (hf : ContDiff ℝ ∞ (lifted f)) :
    ∃ u : Trace, ContDiff ℝ ∞ (lifted u) ∧ ∀ z ∈ closedBall (0:ℂ) 1, ∀ w : Circle,
      Isothermal.geodesicX σ u z w = f z w := by
  obtain ⟨φ,smooth,initial,D,group,geom⟩ := GlobalGeodesicFlow.angularFlow simple.smooth
  let Φ : SmoothFlow State := ⟨φ,smooth,initial,group⟩
  let K := closedBall (0:ℂ) 1 ×ˢ Icc (-Real.pi) Real.pi
  let β (p : State) := Real.smoothTransition (Complex.normSq p.1 - 1)
  have hnorm : ContDiff ℝ ∞ (fun p : State => Complex.normSq p.1) := by
    have re := Complex.reCLM.contDiff.comp (contDiff_fst (E := ℂ) (F := ℝ) (𝕜 := ℝ) (n := ∞))
    have im := Complex.imCLM.contDiff.comp (contDiff_fst (E := ℂ) (F := ℝ) (𝕜 := ℝ) (n := ∞))
    exact (re.mul re).add (im.mul im)
  have hβ : ContDiff ℝ ∞ β := Real.smoothTransition.contDiff.comp (hnorm.sub contDiff_const)
  have inside (p : State) (hp : p ∈ K) : β p = 0 := by
    apply Real.smoothTransition.zero_of_nonpos
    have hb := mem_closedBall_zero_iff.mp hp.1
    rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg p.1]
  have escape (p : State) (hp : p ∈ K) : ∃ t : ℝ, 0 < t ∧ 0 < β (Φ.val (p,-t)) := by
    obtain ⟨t,ht,h⟩ := backward_escape simple (fun r => φ (p,r)) (by simpa [initial] using hp.1)
      (fun r hr => geom p r ((mem_closedBall_zero_iff.mp hr).trans_lt (by norm_num)))
    refine ⟨t,ht,Real.smoothTransition.pos_of_pos ?_⟩
    rw [Complex.normSq_eq_norm_sq]; change 0 < ‖(φ (p,-t)).1‖^2 - 1
    nlinarith
  obtain ⟨τ,hτ,rate,sym⟩ := exists_clock Φ hβ (fun p => Real.smoothTransition.nonneg _) (K := K)
    ((isCompact_closedBall (0:ℂ) 1).prod isCompact_Icc) inside escape
  let U (p : State) := history Φ (lifted f) (p,τ p)
  have ⟨hu,der⟩ := integrate_clock Φ hτ (lifted f) hf
  have uj (c : ℝ) (hc : Circle.exp c = 1) (p : State) : U (shift c p) = U p := by
    have comm := flow_shift simple.smooth Φ D hc
    have t := sym (shift c) comm (fun q => by simp [β,shift]) p
    change history Φ (lifted f) (shift c p,τ (shift c p)) = _
    rw [t]
    change (∫ s in (0:ℝ)..τ p, lifted f (Φ.val (shift c p,-s))) = _
    apply intervalIntegral.integral_congr; intro s _
    dsimp only
    rw [comm]
    simp [lifted,shift,Circle.exp_add,hc]
  let u (z : ℂ) (w : Circle) := U (z,(w:ℂ).arg)
  have eq : lifted u = U := by
    funext p
    let θ := (Circle.exp p.2 : ℂ).arg
    have hθ : Circle.exp θ = Circle.exp p.2 := Circle.exp_arg _
    have hc : Circle.exp (θ-p.2) = 1 := by rw [sub_eq_add_neg,Circle.exp_add,Circle.exp_neg,hθ,mul_inv_cancel]
    have qeq : shift (θ-p.2) p = (p.1,θ) := by ext <;> simp [shift]
    change U (p.1,θ) = U p
    rw [← qeq, uj _ hc]
  have reg : ContDiff ℝ ∞ (lifted u) := eq ▸ hu
  refine ⟨u, reg, ?_⟩
  intro z hz w
  let θ := (w:ℂ).arg
  let p : State := (z,θ)
  have he : Circle.exp θ = w := Circle.exp_arg w
  have hK : p ∈ K := ⟨hz,(Complex.neg_pi_lt_arg _).le,Complex.arg_le_pi _⟩
  have hcurve : HasDerivAt (fun r => φ (p,r)) (chartVector σ p) 0 := by
    have h := geom p 0 (by rw [initial]; exact (mem_closedBall_zero_iff.mp hz).trans_lt (by norm_num))
    simpa only [initial] using h
  have actual := (hu.differentiable (by simp) p).hasFDerivAt.comp_hasDerivAt_of_eq 0 hcurve (initial p).symm
  have result := (der p (rate p hK)).unique actual
  rw [← he,geodesicX_eq_chart_derivative _ _ _ θ (reg.differentiable (by simp) p)]
  change fderiv ℝ (lifted u) p (chartVector σ p) = lifted f p
  rw [eq]
  exact result.symm

/-- An admissible pencil source need only be specified on the open base disk.
Its shifted extension supplies global smooth angular data for unrestricted
integration; the positive conformal multiplier accounts for arclength. -/
theorem pencil_primitive {σ : ℂ → ℝ} (simple : SimpleMetric σ) {rhs : PencilLifts.TraceRHS}
    (h : PencilLifts.ShiftExtends rhs) : ∃ u : Trace, ContDiff ℝ ∞ (lifted u) ∧
    ∀ z ∈ PencilLifts.disk, ∀ w : Circle, Isothermal.geodesicX σ u z w = (Real.exp (-σ z) : ℂ) * rhs z w := by
  obtain ⟨a,ha⟩ := h
  let g (z : ℂ) (w : Circle) := (Real.exp (-σ z) : ℂ) * (starRingEnd ℂ (w:ℂ) * a.val (z,w))
  have angle : ContDiff ℝ ∞ (fun p : State => (Circle.exp p.2 : ℂ)) := by
    simp only [Circle.coe_exp]
    exact ((Complex.ofRealCLM.contDiff.comp contDiff_snd).mul contDiff_const).cexp
  have hg : ContDiff ℝ ∞ (lifted g) := (Complex.ofRealCLM.contDiff.comp (simple.smooth.comp contDiff_fst).neg.exp).mul
    ((Complex.conjCLE.contDiff.comp angle).mul (a.smooth.comp (contDiff_fst.prodMk angle)))
  obtain ⟨u,hu,du⟩ := smooth_primitive simple g hg
  refine ⟨u,hu,?_⟩
  intro z hz w
  rw [du z (ball_subset_closedBall hz)]
  simp [g,ha z hz,← mul_assoc,← Circle.coe_inv_eq_conj]

end TransportOkaGrauert.ScalarGeneralTransport
