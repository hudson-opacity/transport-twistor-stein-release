import TransportOkaGrauert.ChartStein
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-! # Ordinary complex derivatives in transport CR coordinates -/

noncomputable section
namespace TransportOkaGrauert.CRCoordinates

open Complex ChartStein Filter
open scoped Topology ContDiff

private def coefficient (p : E) := I * (1 - p.2 ^ 2)

private theorem coefficient_ne {p : E} (hw : ‖p.2‖ < 1) : coefficient p ≠ 0 := by
  apply mul_ne_zero I_ne_zero
  intro hz
  have h : ‖p.2‖ ^ 2 = 1 := by
    rw [← norm_pow, (sub_eq_zero.mp hz).symm, norm_one]
  nlinarith [sq_nonneg (1 - ‖p.2‖), norm_nonneg p.2,
    mul_pos (sub_pos.mpr hw) (show 0 < 1 + ‖p.2‖ by positivity)]

private def coframe (σ : ℂ → ℝ) (p v : E) : E :=
  ((v.1.re : ℂ) + (v.1.im : ℂ) * (-(1 + p.2^2) / coefficient p),
   v.2 + (v.1.im : ℂ) * (connectionCoefficient σ p / coefficient p))

private def row (D : E →L[ℝ] ℂ) : E →L[ℂ] ℂ :=
  D (1,0) • ContinuousLinearMap.fst ℂ ℂ ℂ + D (0,1) • ContinuousLinearMap.snd ℂ ℂ ℂ

/-- Every CR covector has two complex coefficients in the same coframe. -/
private theorem factors {σ : ℂ → ℝ} {p : E} (hw : ‖p.2‖ < 1)
    {D : E →L[ℝ] ℂ} (hD : SatisfiesCR σ p D) (v : E) :
    row D (coframe σ p v) = D v := by
  obtain ⟨hv, hh⟩ := hD
  have e : v = (v.1.re • ((1,0) : E) + v.1.im • ((I,0) : E)) +
      (v.2.re • ((0,1) : E) + v.2.im • ((0,I) : E)) := by
    ext <;> simp [Complex.real_smul]
  conv_rhs => rw [e, map_add, map_add, map_add, map_smul, map_smul, map_smul, map_smul, hv]
  change D (1,0) * ((v.1.re : ℂ) + (v.1.im : ℂ) * (-(1 + p.2^2) / coefficient p)) +
    D (0,1) * (v.2 + (v.1.im : ℂ) * (connectionCoefficient σ p / coefficient p)) = _
  simp only [Complex.real_smul]
  conv_lhs => arg 2; arg 2; arg 1; rw [← Complex.re_add_im v.2]
  field_simp [coefficient_ne hw]
  unfold coefficient
  linear_combination -((v.1.im : ℂ) * hh)

/-- Invertible CR coordinates make any other CR differential ordinary
complex-linear. The factor is a genuine complex continuous linear map. -/
theorem factor_through_pair {σ : ℂ → ℝ} {p : E} (hw : ‖p.2‖ < 1)
    {A B H : E →L[ℝ] ℂ} (ha : SatisfiesCR σ p A) (hb : SatisfiesCR σ p B)
    (hh : SatisfiesCR σ p H) (hp : Function.Bijective (A.prod B)) :
    ∃ L : E →L[ℂ] ℂ, ∀ v : E, L (A v, B v) = H v := by
  let M := (row A).prod (row B)
  have hm (v : E) : M (coframe σ p v) = (A v, B v) :=
    Prod.ext (factors hw ha v) (factors hw hb v)
  have hsur : Function.Surjective M := by
    intro y
    obtain ⟨x, hx⟩ := hp.2 y
    exact ⟨coframe σ p x, (hm x).trans hx⟩
  have hinj : Function.Injective M := LinearMap.injective_iff_surjective.mpr
    (show Function.Surjective M.toLinearMap from hsur)
  let T := ContinuousLinearEquiv.ofBijective M (LinearMap.ker_eq_bot.mpr hinj)
    (LinearMap.range_eq_top.mpr hsur)
  refine ⟨(row H).comp T.symm.toContinuousLinearMap, fun v => ?_⟩
  change row H (T.symm (A v, B v)) = H v
  rw [← hm v, show M (coframe σ p v) = T (coframe σ p v) from rfl, T.symm_apply_apply]
  exact factors hw hh v

/-- A scalar CR function expressed in an existing real coordinate chart has
an ordinary complex derivative wherever the chart coordinates are CR and
their real differential is invertible. -/
theorem differentiableAt_in_chart {σ : ℂ → ℝ} {p : E} (hw : ‖p.2‖ < 1)
    {f g h : E → ℂ} (hf : HolAt σ f p) (hg : HolAt σ g p) (hh : HolAt σ h p)
    (e : OpenPartialHomeomorph E E) (he : (e : E → E) = (fun x => (f x, g x))) (hx : p ∈ e.source)
    (hbij : Function.Bijective (fderiv ℝ (fun x => (f x,g x)) p)) :
    DifferentiableAt ℂ (h ∘ e.symm) (e p) := by
  let A := fderiv ℝ f p
  let B := fderiv ℝ g p
  let H := fderiv ℝ h p
  have hd : HasFDerivAt (fun x => (f x, g x)) (A.prod B) p :=
    (hf.1.differentiableAt (by simp)).hasFDerivAt.prodMk (hg.1.differentiableAt (by simp)).hasFDerivAt
  have hp : Function.Bijective (A.prod B) := hd.fderiv ▸ hbij
  let T := ContinuousLinearEquiv.ofBijective (A.prod B) (LinearMap.ker_eq_bot.mpr hp.1)
    (LinearMap.range_eq_top.mpr hp.2)
  obtain ⟨L,hL⟩ := factor_through_pair hw (H := H) hf.2 hg.2 hh.2 hp
  have he' : e.symm (e p) = p := e.left_inv hx
  have hi : HasFDerivAt (e.symm : E → E) T.symm.toContinuousLinearMap (e p) := by
    apply e.hasFDerivAt_symm (e.map_source hx)
    rw [he', he]
    exact hd
  have dH : HasFDerivAt h H (e.symm (e p)) := by
    rw [he']
    exact (hh.1.differentiableAt (by simp)).hasFDerivAt
  refine (hasFDerivAt_of_restrictScalars ℝ (dH.comp _ hi) (f' := L) ?_).differentiableAt
  apply ContinuousLinearMap.ext
  intro v
  change L v = H (T.symm v)
  exact (congrArg L (T.apply_symm_apply v).symm).trans (hL (T.symm v))

/-- An invertible CR pair supplies a real local coordinate homeomorphism.
Every other CR function has an ordinary complex derivative after composition
with its local inverse at the chart centre. -/
theorem local_coordinates {σ : ℂ → ℝ} {p : E} (hw : ‖p.2‖ < 1)
    {f g : E → ℂ} (hf : HolAt σ f p) (hg : HolAt σ g p)
    (hbij : Function.Bijective (fderiv ℝ (fun x => (f x, g x)) p)) :
    ∃ e : OpenPartialHomeomorph E E, (e : E → E) = (fun x => (f x, g x)) ∧ p ∈ e.source ∧
      ∀ h : E → ℂ, HolAt σ h p → DifferentiableAt ℂ (h ∘ e.symm) (e p) := by
  let F := fun x => (f x,g x)
  let A := fderiv ℝ f p
  let B := fderiv ℝ g p
  have hd : HasFDerivAt F (A.prod B) p :=
    (hf.1.differentiableAt (by simp)).hasFDerivAt.prodMk (hg.1.differentiableAt (by simp)).hasFDerivAt
  have hp : Function.Bijective (A.prod B) := hd.fderiv ▸ hbij
  let T := ContinuousLinearEquiv.ofBijective (A.prod B) (LinearMap.ker_eq_bot.mpr hp.1)
    (LinearMap.range_eq_top.mpr hp.2)
  have dh : HasStrictFDerivAt F T.toContinuousLinearMap p :=
    (hf.1.prodMk hg.1).hasStrictFDerivAt' hd (by simp)
  let e := dh.toOpenPartialHomeomorph F
  refine ⟨e,rfl,dh.mem_toOpenPartialHomeomorph_source, ?_⟩
  intro h hh
  exact differentiableAt_in_chart hw hf hg hh e rfl dh.mem_toOpenPartialHomeomorph_source hbij

/-- An invertible CR pair defines an open coordinate chart throughout which
every CR function is ordinarily holomorphic. Applying this to the two components
of another coordinate chart gives ordinary holomorphic transition functions
on chart overlaps. -/
theorem holomorphic_chart {σ : ℂ → ℝ} {p : E} {O : Set E} (hO : IsOpen O) (hpO : p ∈ O)
    (hvel : ∀ x ∈ O, ‖x.2‖ < 1) {f g : E → ℂ}
    (hf : ∀ x ∈ O, HolAt σ f x) (hg : ∀ x ∈ O, HolAt σ g x)
    (hbij : Function.Bijective (fderiv ℝ (fun x => (f x, g x)) p)) :
    ∃ e : OpenPartialHomeomorph E E, (e : E → E) = (fun x => (f x, g x)) ∧
      p ∈ e.source ∧ e.source ⊆ O ∧
      ∀ h : E → ℂ, (∀ x ∈ e.source, HolAt σ h x) → DifferentiableOn ℂ (h ∘ e.symm) e.target := by
  let F (x : E) := (f x, g x)
  have dF := (hf p hpO).1.prodMk (hg p hpO).1
  have hd : ContinuousAt (fderiv ℝ F) p := dF.continuousAt_fderiv (by simp)
  have hu : ∀ᶠ x in 𝓝 p, IsUnit (fderiv ℝ F x) :=
    hd.eventually (Units.isOpen.mem_nhds (ContinuousLinearMap.isUnit_iff_bijective.mpr hbij))
  have hboth : O ∩ {x | IsUnit (fderiv ℝ F x)} ∈ 𝓝 p := inter_mem (hO.mem_nhds hpO) hu
  obtain ⟨W,hW,ho,hp⟩ := mem_nhds_iff.mp hboth
  obtain ⟨e,he,hp',_⟩ := local_coordinates (hvel p hpO) (hf p hpO) (hg p hpO) hbij
  let e' := e.restr W
  have src : e'.source = e.source ∩ W := e.restr_source' W ho
  have hc : (e' : E → E) = F := he
  have sub : e'.source ⊆ O := fun x hx => (hW ((src ▸ hx).2)).1
  refine ⟨e',hc,src ▸ ⟨hp',hp⟩,sub, ?_⟩
  intro h hh y hy
  let x := e'.symm y
  have hx : x ∈ e'.source := e'.map_target hy
  have hb : Function.Bijective (fderiv ℝ F x) :=
    ContinuousLinearMap.isUnit_iff_bijective.mp (hW ((src ▸ hx).2)).2
  have H := differentiableAt_in_chart (hvel x (sub hx)) (hf x (sub hx)) (hg x (sub hx))
    (hh x hx) e' hc hx hb
  simpa only [x, e'.right_inv hy] using H.differentiableWithinAt (s := e'.target)

/-- Ordinary complex-linear combinations of a CR pair satisfy the two
transport equations. -/
theorem cr_of_complex_linear {σ : ℂ → ℝ} {p : E} {A B : E →L[ℝ] ℂ}
    (ha : SatisfiesCR σ p A) (hb : SatisfiesCR σ p B) (L : E →L[ℂ] ℂ) :
    SatisfiesCR σ p ((L.restrictScalars ℝ).comp (A.prod B)) := by
  have split (x y : ℂ) : L (x,y) = x * L (1,0) + y * L (0,1) := by
    have he : (x,y) = x • ((1,0) : E) + y • ((0,1) : E) := by simp
    conv_lhs => rw [he, map_add, map_smul, map_smul]
    rfl
  constructor
  · change L (A (0,I),B (0,I)) = I * L (A (0,1),B (0,1))
    rw [split (A (0,I)) (B (0,I)), split (A (0,1)) (B (0,1)), ha.1, hb.1]
    ring
  · change p.2^2 * (L (A (1,0), B (1,0)) - I * L (A (I,0), B (I,0))) +
      (L (A (1,0), B (1,0)) + I * L (A (I,0), B (I,0))) -
      connectionCoefficient σ p * L (A (0,1), B (0,1)) = 0
    rw [split (A (1,0)) (B (1,0)), split (A (I,0)) (B (I,0)), split (A (0,1)) (B (0,1))]
    linear_combination L (1,0) * ha.2 + L (0,1) * hb.2

/-- Conversely, an ordinary analytic function of a transport CR coordinate
pair is transport holomorphic. This direction also holds for a singular pair. -/
theorem holAt_of_analytic_coordinates {σ : ℂ → ℝ} {p : E} {f g : E → ℂ}
    (hf : HolAt σ f p) (hg : HolAt σ g p) {H : E → ℂ} (hH : AnalyticAt ℂ H (f p, g p)) :
    HolAt σ (H ∘ (fun x => (f x,g x))) p := by
  have dH := hH.differentiableAt.hasFDerivAt
  have dfg := (hf.1.differentiableAt (by simp)).hasFDerivAt.prodMk
    (hg.1.differentiableAt (by simp)).hasFDerivAt
  refine ⟨((hH.contDiffAt (n := ∞)).restrict_scalars ℝ).comp p (hf.1.prodMk hg.1), ?_⟩
  rw [((dH.restrictScalars ℝ).comp p dfg).fderiv]
  exact cr_of_complex_linear hf.2 hg.2 _

end TransportOkaGrauert.CRCoordinates
