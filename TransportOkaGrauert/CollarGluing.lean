import TransportOkaGrauert.FrameLevi
import TransportOkaGrauert.ConformalCollar
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Gluing strictly plurisubharmonic collar potentials

A primitive of the monotone smooth transition supplies an exact inactive
branch and has nonnegative second derivative. The Levi calculation uses
the exterior derivative of `-df ∘ J` from the transport frame.
-/

noncomputable section
namespace TransportOkaGrauert.CollarGluing

open Real Filter Set MeasureTheory FrameLevi
open scoped ContDiff Topology Interval

/-- Smooth convex replacement for the positive part. -/
def ramp (t : ℝ) : ℝ := ∫ s in (0 : ℝ)..t, smoothTransition s

theorem ramp_deriv (t : ℝ) : HasDerivAt ramp (smoothTransition t) t :=
  intervalIntegral.integral_hasDerivAt_right (smoothTransition.continuous.intervalIntegrable _ _)
    smoothTransition.continuous.stronglyMeasurable.stronglyMeasurableAtFilter
    smoothTransition.continuousAt

theorem ramp_smooth : ContDiff ℝ ∞ ramp := by
  apply contDiff_infty_iff_deriv.mpr
  exact ⟨fun t => (ramp_deriv t).differentiableAt,
    (funext fun t => (ramp_deriv t).deriv) ▸ smoothTransition.contDiff⟩

theorem ramp_inactive {t : ℝ} (ht : t ≤ 0) : ramp t = 0 := by
  calc
    ramp t = ∫ _ in (0 : ℝ)..t, (0 : ℝ) :=
      intervalIntegral.integral_congr fun s hs =>
        smoothTransition.zero_of_nonpos ((uIcc_of_ge ht ▸ hs).2)
    _ = 0 := by simp

theorem ramp_active {t : ℝ} (ht : 1 ≤ t) : ramp t = ramp 1 + t - 1 := by
  have h : (∫ s in (1 : ℝ)..t, smoothTransition s) = t - 1 := by
    calc
      _ = ∫ _ in (1 : ℝ)..t, (1 : ℝ) :=
        intervalIntegral.integral_congr fun s hs =>
          smoothTransition.one_of_one_le ((uIcc_of_le ht ▸ hs).1)
      _ = _ := by simp
  unfold ramp
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (smoothTransition.continuous.intervalIntegrable 0 1)
    (smoothTransition.continuous.intervalIntegrable 1 t), h]
  ring

theorem ramp_nonneg (t : ℝ) : 0 ≤ ramp t := by
  rcases le_total t 0 with h | h
  · simp [ramp_inactive h]
  · exact intervalIntegral.integral_nonneg h (fun s _ => smoothTransition.nonneg s)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def blend (f g : E → ℝ) (p : E) : ℝ := f p + ramp (g p - f p)

theorem blend_smooth {f g : E → ℝ} {p : E} (hf : ContDiffAt ℝ ∞ f p) (hg : ContDiffAt ℝ ∞ g p) :
    ContDiffAt ℝ ∞ (blend f g) p :=
  hf.add (ramp_smooth.contDiffAt.comp p (hg.sub hf))

private def component (J : E → E →L[ℝ] E) (f : E → ℝ) (w y : E) : ℝ :=
  -fderiv ℝ f y (J y w)

private theorem component_diff {J : E → E →L[ℝ] E} {f : E → ℝ} {p : E}
    (hJ : DifferentiableAt ℝ J p) (hf : ContDiffAt ℝ 2 f p) (w : E) :
    DifferentiableAt ℝ (component J f w) p :=
  (((hf.fderiv_right (m := 1) (by decide)).differentiableAt one_ne_zero).clm_apply
    (hJ.clm_apply (differentiableAt_const w))).neg

private theorem ddC_eq {J : E → E →L[ℝ] E} {f : E → ℝ} {p : E}
    (hJ : DifferentiableAt ℝ J p) (hf : ContDiffAt ℝ 2 f p) (v w : E) :
    ddC J f p v w = fderiv ℝ (component J f w) p v - fderiv ℝ (component J f v) p w := by
  have hd := (hf.fderiv_right (m := 1) (by decide)).differentiableAt one_ne_zero
  have hform : DifferentiableAt ℝ (dc J f) p :=
    (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℝ) (0 : Fin 1)).differentiableAt.comp
      p (hd.clm_comp hJ).neg
  have rem0 : (0 : Fin 2).removeNth ![v,w] = ![w] := by funext i; fin_cases i; rfl
  have rem1 : (1 : Fin 2).removeNth ![v,w] = ![v] := by funext i; fin_cases i; rfl
  rw [ddC, extDeriv_apply hform]
  simp only [Nat.reduceAdd, Fin.sum_univ_two, rem0, rem1, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
    one_smul, neg_one_smul, Matrix.cons_val_zero, Matrix.cons_val_one, sub_eq_add_neg]
  rfl

private theorem component_blend {J : E → E →L[ℝ] E} {f g : E → ℝ} {p : E}
    (hf : DifferentiableAt ℝ f p) (hg : DifferentiableAt ℝ g p) (v : E) :
    component J (blend f g) v p = component J f v p +
      smoothTransition (g p - f p) * (component J g v p - component J f v p) := by
  have h := hf.hasFDerivAt.add ((ramp_deriv (g p - f p)).comp_hasFDerivAt p
    (hg.hasFDerivAt.sub hf.hasFDerivAt))
  change HasFDerivAt (blend f g) _ p at h
  simp [component, h.fderiv]
  ring

/-- Exact Levi chain rule for the smooth maximum. Its last term is the
nonnegative correction from convexity, also for a nonconstant `J`. -/
theorem ddC_blend {J : E → E →L[ℝ] E} {f g : E → ℝ} {p : E}
    (hJ : DifferentiableAt ℝ J p) (hf : ContDiffAt ℝ 2 f p) (hg : ContDiffAt ℝ 2 g p)
    (v : E) (hJJ : J p (J p v) = -v) :
    let q := smoothTransition (g p - f p)
    ddC J (blend f g) p v (J p v) = (1-q) * ddC J f p v (J p v) +
      q * ddC J g p v (J p v) + deriv smoothTransition (g p - f p) *
        ((fderiv ℝ g p v - fderiv ℝ f p v)^2 +
          (fderiv ℝ g p (J p v) - fderiv ℝ f p (J p v))^2) := by
  let q := fun y => smoothTransition (g y - f y)
  have dq := (smoothTransition.contDiffAt (n := 1) (x := g p - f p)).differentiableAt one_ne_zero
  have hq := dq.hasDerivAt.comp_hasFDerivAt p
    ((hg.differentiableAt (by decide)).hasFDerivAt.sub (hf.differentiableAt (by decide)).hasFDerivAt)
  have hblend : ContDiffAt ℝ 2 (blend f g) p :=
    hf.add ((ramp_smooth.of_le (by decide)).contDiffAt.comp p (hg.sub hf))
  have derivative (w u : E) :
      fderiv ℝ (component J (blend f g) w) p u =
        fderiv ℝ (component J f w) p u +
        q p * (fderiv ℝ (component J g w) p u - fderiv ℝ (component J f w) p u) +
        (component J g w p - component J f w p) * deriv smoothTransition (g p - f p) *
          (fderiv ℝ g p u - fderiv ℝ f p u) := by
    have cf := (component_diff hJ hf w).hasFDerivAt
    have cg := (component_diff hJ hg w).hasFDerivAt
    have h := cf.add (hq.mul (cg.sub cf))
    have actual := h.congr_of_eventuallyEq (f₁ := component J (blend f g) w) (by
      filter_upwards [hf.eventually (by decide), hg.eventually (by decide)] with y hy hy'
      exact component_blend (hy.differentiableAt (by decide)) (hy'.differentiableAt (by decide)) w)
    rw [actual.fderiv]
    simp [q]
    ring
  rw [ddC_eq hJ hblend, ddC_eq hJ hf, ddC_eq hJ hg, derivative, derivative]
  simp [component, hJJ, q]
  ring

/-- Strict positivity of the actual real Levi form on complex lines at `p`. -/
def StrictAt (J : E → E →L[ℝ] E) (f : E → ℝ) (p : E) : Prop :=
  ∀ v : E, v ≠ 0 → 0 < ddC J f p v (J p v)

/-- Only branches whose transition coefficient is positive need strict
Levi positivity. This allows an arbitrary smooth extension of an inactive
branch to the inside of its collar. -/
theorem strict_blend {J : E → E →L[ℝ] E} {f g : E → ℝ} {p : E}
    (hJ : DifferentiableAt ℝ J p) (JJ : ∀ v, J p (J p v) = -v)
    (hf : ContDiffAt ℝ 2 f p) (hg : ContDiffAt ℝ 2 g p)
    (pf : g p - f p < 1 → StrictAt J f p) (pg : 0 < g p - f p → StrictAt J g p) :
    StrictAt J (blend f g) p := by
  intro v hv
  rw [ddC_blend hJ hf hg v (JJ v)]
  let q := smoothTransition (g p - f p)
  have plus : 0 ≤ deriv smoothTransition (g p - f p) *
      ((fderiv ℝ g p v - fderiv ℝ f p v)^2 +
        (fderiv ℝ g p (J p v) - fderiv ℝ f p (J p v))^2) :=
    mul_nonneg smoothTransition.monotone.deriv_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _))
  apply add_pos_of_pos_of_nonneg _ plus
  by_cases hz : g p - f p ≤ 0
  · simpa [smoothTransition.zero_of_nonpos hz] using pf (lt_of_le_of_lt hz zero_lt_one) v hv
  by_cases ho : 1 ≤ g p - f p
  · simpa [smoothTransition.one_of_one_le ho] using pg (lt_of_lt_of_le zero_lt_one ho) v hv
  exact add_pos (mul_pos (sub_pos.mpr (smoothTransition.lt_one_of_lt_one (lt_of_not_ge ho)))
    (pf (lt_of_not_ge ho) v hv)) (mul_pos (smoothTransition.pos_of_pos (lt_of_not_ge hz))
      (pg (lt_of_not_ge hz) v hv))

theorem strict_sub_const {J : E → E →L[ℝ] E} {f : E → ℝ} {p : E}
    (h : StrictAt J f p) (c : ℝ) : StrictAt J (fun y => f y - c) p := by
  have eq : dc J (fun y => f y - c) = dc J f := by
    funext y
    simp only [dc, fderiv_sub_const]
  simpa only [StrictAt, ddC, eq] using h

/-- The interior in a smooth trivialization of the two closed disks. -/
abbrev DiskProduct := ℂ × ℂ

def domain : Set DiskProduct := {p | ‖p.1‖ < 1 ∧ ‖p.2‖ < 1}

/-- Uniform blowup of a single disk barrier at its circle. -/
def Escapes (a : ℂ → ℝ) : Prop :=
  ∀ c : ℝ, ∃ r < 1, ∀ z : ℂ, r < ‖z‖ → ‖z‖ < 1 → c < a z

private def rectangle (b v : ℝ) : Set DiskProduct :=
  Metric.closedBall (0 : ℂ) b ×ˢ Metric.closedBall (0 : ℂ) v

private theorem compact_rectangle (b v : ℝ) : IsCompact (rectangle b v) :=
  (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)

private theorem mem_rectangle {p : DiskProduct} {b v : ℝ} :
    p ∈ rectangle b v ↔ ‖p.1‖ ≤ b ∧ ‖p.2‖ ≤ v :=
  and_congr mem_closedBall_zero_iff mem_closedBall_zero_iff

private theorem rectangle_subset {b v : ℝ} (hb : b < 1) (hv : v < 1) :
    rectangle b v ⊆ domain := fun _ hp =>
  ⟨(mem_rectangle.mp hp).1.trans_lt hb, (mem_rectangle.mp hp).2.trans_lt hv⟩

private theorem compact_sublevel {h : DiskProduct → ℝ} (c : ℝ) {b v : ℝ}
    (hb : b < 1) (hv : v < 1) (hc : ContinuousOn h domain)
    (bound : ∀ p ∈ domain, h p ≤ c → p ∈ rectangle b v) :
    IsCompact {p ∈ domain | h p ≤ c} := by
  let K := rectangle b v
  letI : CompactSpace K := isCompact_iff_compactSpace.mp (compact_rectangle b v)
  have ch : Continuous (fun p : K => h p.val) :=
    continuousOn_iff_continuous_restrict.mp (hc.mono (rectangle_subset hb hv))
  have closed : IsClosed {p : K | h p.val ≤ c} := isClosed_le ch continuous_const
  have eq : {p ∈ domain | h p ≤ c} = Subtype.val '' {p : K | h p.val ≤ c} := by
    ext p
    constructor
    · rintro ⟨hp,hp'⟩
      exact ⟨⟨p, bound p hp hp'⟩, hp', rfl⟩
    · rintro ⟨q, hq, rfl⟩
      exact ⟨rectangle_subset hb hv q.property, hq⟩
  rw [eq]
  exact closed.isCompact.image continuous_subtype_val

/-- Construct the shifted smooth maximum on the full disk product. The
velocity branch differs by a bounded amount from its radial barrier `u`.
The other branch is `u+a`, where the base summand has a smooth extension
through the inner edge of the base collar and diverges at its boundary.
The inputs ask for strict positivity of each branch only on its own collar.
Both the compact exceptional set and each compact sublevel are constructed. -/
theorem glue_exhaustion (J : DiskProduct → DiskProduct →L[ℝ] DiskProduct)
    (u a : ℂ → ℝ) (f : DiskProduct → ℝ) (C rb rv : ℝ) (hrb : rb < 1) (hrv : rv < 1)
    (du : ∀ z : ℂ, ‖z‖ < 1 → ContDiffAt ℝ ∞ u z)
    (da : ∀ z : ℂ, ‖z‖ < 1 → ContDiffAt ℝ ∞ a z)
    (df : ∀ p ∈ domain, ContDiffAt ℝ ∞ f p)
    (eu : Escapes u) (ea : Escapes a) (upos : ∀ z : ℂ, ‖z‖ < 1 → 0 ≤ u z)
    (gap : ∀ p ∈ domain, |f p - u p.2| ≤ C)
    (dJ : ∀ p ∈ domain, DifferentiableAt ℝ J p)
    (JJ : ∀ p ∈ domain, ∀ v, J p (J p v) = -v)
    (velocity : ∀ p ∈ domain, rv < ‖p.2‖ → StrictAt J f p)
    (base : ∀ p ∈ domain, rb < ‖p.1‖ → StrictAt J (fun y => u y.2 + a y.1) p) :
    ∃ L : ℝ, let h := blend f (fun y => u y.2 + a y.1 - L)
      (∀ p ∈ domain, ContDiffAt ℝ ∞ h p) ∧ (∀ c : ℝ, IsCompact {p ∈ domain | h p ≤ c}) ∧
      ∃ K : Set DiskProduct, IsCompact K ∧ K ⊆ domain ∧ ∀ p ∈ domain, p ∉ K → StrictAt J h p := by
  have ca : ContinuousOn a (Metric.closedBall (0 : ℂ) rb) := fun z hz =>
    (da z ((mem_closedBall_zero_iff.mp hz).trans_lt hrb)).continuousAt.continuousWithinAt
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) rb).bddAbove_image ca
  let L := M + C
  let g := fun p : DiskProduct => u p.2 + a p.1 - L
  have dg (p : DiskProduct) (hp : p ∈ domain) : ContDiffAt ℝ ∞ g p :=
    (((du p.2 hp.2).comp p contDiffAt_snd).add ((da p.1 hp.1).comp p contDiffAt_fst)).sub contDiffAt_const
  let h := blend f g
  have dh (p : DiskProduct) (hp : p ∈ domain) : ContDiffAt ℝ ∞ h p := blend_smooth (df p hp) (dg p hp)
  refine ⟨L, dh, ?_, ?_⟩
  · intro c
    obtain ⟨s, hs, hbase⟩ := ea (c + L + 1)
    obtain ⟨t, ht, hvel⟩ := eu (c + C)
    apply compact_sublevel c hs ht (fun p hp => (dh p hp).continuousAt.continuousWithinAt)
    intro p hp hc
    have hfbound : f p ≤ c := le_trans (le_add_of_nonneg_right (ramp_nonneg _)) hc
    have hu := abs_le.mp (gap p hp)
    apply mem_rectangle.mpr
    constructor
    · by_contra! hb
      have ha := hbase p.1 hb hp.1
      have u0 := upos p.2 hp.2
      have hlarge : 1 ≤ g p - f p := by dsimp [g]; linarith
      change f p + ramp (g p - f p) ≤ c at hc
      rw [ramp_active hlarge] at hc
      dsimp [g] at hc
      linarith [ramp_nonneg 1]
    · by_contra! hv
      linarith [hvel p.2 hv hp.2]
  · obtain ⟨s, hs, houter⟩ := ea (L + C + 1)
    refine ⟨rectangle s rv, compact_rectangle _ _, rectangle_subset hs hrv, ?_⟩
    intro p hp hK
    apply strict_blend (dJ p hp) (JJ p hp) ((df p hp).of_le (by decide))
      ((dg p hp).of_le (by decide))
    · intro hgap
      apply velocity p hp
      by_contra! hv
      have ho : s < ‖p.1‖ := lt_of_not_ge fun he => hK (mem_rectangle.mpr ⟨he, hv⟩)
      have ha := houter p.1 ho hp.1
      have hupper := (abs_le.mp (gap p hp)).2
      dsimp [g] at hgap
      linarith
    · intro hgap
      apply strict_sub_const _ L
      apply base p hp
      by_contra! hb
      have ha := hM (mem_image_of_mem a (mem_closedBall_zero_iff.mpr hb))
      have hlower := (abs_le.mp (gap p hp)).1
      dsimp [g, L] at hgap
      linarith

open ConformalCollar

/-- The standard logarithmic barrier of the velocity disk. -/
def diskBarrier (z : ℂ) : ℝ := -log (b₀ z)

/-- Extend the base defining function smoothly by one on the inside of the
disk. The transition occurs where the polynomial is already positive. -/
def extendedDefining (L : ℝ) (z : ℂ) : ℝ :=
  let χ := smoothTransition (4 * L * b₀ z - 1)
  (1-χ) * defining L z + χ

def baseBarrier (L : ℝ) (z : ℂ) : ℝ := -log (extendedDefining L z)

private theorem smooth_b₀ : ContDiff ℝ ∞ b₀ := by
  have eq : b₀ = fun z : ℂ => 1 - (z.re ^ 2 + z.im ^ 2) := by
    funext z
    simp [b₀, Complex.normSq_apply, pow_two]
  rw [eq]
  exact contDiff_const.sub ((Complex.reCLM.contDiff.pow 2).add (Complex.imCLM.contDiff.pow 2))

private theorem positive_b₀ {z : ℂ} (hz : ‖z‖ < 1) : 0 < b₀ z := by
  rw [b₀, Complex.normSq_eq_norm_sq]
  nlinarith [norm_nonneg z]

private theorem small_b₀ {ε : ℝ} (hε : 0 < ε) :
    ∃ r < 1, ∀ z : ℂ, r < ‖z‖ → ‖z‖ < 1 → b₀ z < ε := by
  refine ⟨1-ε/2, by linarith, ?_⟩
  intro z hr hz
  rw [b₀, Complex.normSq_eq_norm_sq]
  nlinarith [sq_nonneg (1-‖z‖)]

theorem diskBarrier_smooth {z : ℂ} (hz : ‖z‖ < 1) : ContDiffAt ℝ ∞ diskBarrier z :=
  (smooth_b₀.contDiffAt.log (positive_b₀ hz).ne').neg

theorem diskBarrier_nonneg {z : ℂ} (hz : ‖z‖ < 1) : 0 ≤ diskBarrier z := by
  exact neg_nonneg.mpr (log_nonpos (positive_b₀ hz).le (sub_le_self _ (Complex.normSq_nonneg _)))

theorem diskBarrier_escapes : Escapes diskBarrier := by
  intro c
  obtain ⟨r, hr, h⟩ := small_b₀ (exp_pos (-c))
  exact ⟨r, hr, fun z hz hz' => by
    have hlog := (log_lt_iff_lt_exp (positive_b₀ hz')).mpr (h z hz hz')
    change c < -log (b₀ z)
    linarith⟩

private theorem extended_pos {L : ℝ} {z : ℂ} (hz : ‖z‖ < 1) :
    0 < extendedDefining L z := by
  let s := 4 * L * b₀ z - 1
  by_cases h : 1 ≤ s
  · simp [extendedDefining, smoothTransition.one_of_one_le (show 1 ≤ 4 * L * b₀ z - 1 from h)]
  · have hc : 0 < 1 - smoothTransition s :=
      sub_pos.mpr (smoothTransition.lt_one_of_lt_one (lt_of_not_ge h))
    have hb : 0 < defining L z := by
      rw [show defining L z = b₀ z * (1 - L * b₀ z) by unfold defining; ring]
      apply mul_pos (positive_b₀ hz)
      dsimp [s] at h
      linarith
    exact add_pos_of_pos_of_nonneg (mul_pos hc hb) (smoothTransition.nonneg s)

private theorem extended_smooth (L : ℝ) : ContDiff ℝ ∞ (extendedDefining L) := by
  have hc := (smoothTransition.contDiff (n := ⊤)).comp
    (((contDiff_const (c := 4 * L)).mul smooth_b₀).sub (contDiff_const (c := (1 : ℝ))))
  exact ((contDiff_const.sub hc).mul
    (smooth_b₀.sub (contDiff_const.mul (smooth_b₀.pow 2)))).add hc

theorem baseBarrier_smooth (L : ℝ) {z : ℂ} (hz : ‖z‖ < 1) :
    ContDiffAt ℝ ∞ (baseBarrier L) z := ((extended_smooth L).contDiffAt.log (extended_pos (L := L) hz).ne').neg

private theorem extended_eq {L : ℝ} {z : ℂ} (h : 4 * L * b₀ z ≤ 1) :
    extendedDefining L z = defining L z := by
  simp [extendedDefining, smoothTransition.zero_of_nonpos (sub_nonpos.mpr h)]

theorem baseBarrier_escapes {L : ℝ} (hL : 0 < L) : Escapes (baseBarrier L) := by
  intro c
  obtain ⟨r, hr, hs⟩ := small_b₀ (lt_min (exp_pos (-c)) (by positivity : 0 < 1/(4*L)))
  refine ⟨r, hr, ?_⟩
  intro z hz hz'
  have h := hs z hz hz'
  have hsmall := (lt_div_iff₀ (by positivity : 0 < 4*L)).mp (lt_min_iff.mp h).2
  have eq := extended_eq (L := L) (z := z) (by linarith)
  have hbound : extendedDefining L z < exp (-c) := by
    rw [eq, defining]
    exact (sub_le_self _ (mul_nonneg hL.le (sq_nonneg _))).trans_lt (lt_min_iff.mp h).1
  have hlog := (log_lt_iff_lt_exp (extended_pos (L := L) hz')).mpr hbound
  change c < -log (extendedDefining L z)
  linarith

/-- Germ equivalence preserves the actual exterior derivative defining
strict plurisubharmonicity. -/
theorem StrictAt.congr {J : E → E →L[ℝ] E} {f g : E → ℝ} {p : E}
    (hf : StrictAt J f p) (hfg : f =ᶠ[𝓝 p] g) : StrictAt J g p := by
  have hd : dc J f =ᶠ[𝓝 p] dc J g := by
    filter_upwards [hfg.fderiv (𝕜 := ℝ)] with y hy
    simp only [dc, hy]
  simpa only [StrictAt, ddC, hd.extDeriv_eq] using hf

/-- The two logarithmic boundary branches of the conformal disk yield a
smooth proper exhaustion strictly plurisubharmonic off a compact set. The
remaining geometric inputs are the chart's complex structure and strict
Levi inequalities on the original, unextended branches in their collars. -/
theorem logarithmic_collar_exhaustion (J : DiskProduct → DiskProduct →L[ℝ] DiskProduct)
    (f : DiskProduct → ℝ) (L C rb rv : ℝ) (hL : 0 < L) (hrb : rb < 1) (hrv : rv < 1)
    (df : ∀ p ∈ domain, ContDiffAt ℝ ∞ f p) (gap : ∀ p ∈ domain, |f p - diskBarrier p.2| ≤ C)
    (dJ : ∀ p ∈ domain, DifferentiableAt ℝ J p) (JJ : ∀ p ∈ domain, ∀ v, J p (J p v) = -v)
    (velocity : ∀ p ∈ domain, rv < ‖p.2‖ → StrictAt J f p)
    (base : ∀ p ∈ domain, rb < ‖p.1‖ →
      StrictAt J (fun y => diskBarrier y.2 - log (defining L y.1)) p) :
    ∃ c : ℝ, let h := blend f (fun y => diskBarrier y.2 + baseBarrier L y.1 - c)
      (∀ p ∈ domain, ContDiffAt ℝ ∞ h p) ∧ (∀ m : ℝ, IsCompact {p ∈ domain | h p ≤ m}) ∧
      ∃ K : Set DiskProduct, IsCompact K ∧ K ⊆ domain ∧ ∀ p ∈ domain, p ∉ K → StrictAt J h p := by
  obtain ⟨s, hs, hcut⟩ := small_b₀ (by positivity : 0 < 1/(4*L))
  apply glue_exhaustion J diskBarrier (baseBarrier L) f C (max rb s) rv (max_lt hrb hs) hrv
    (fun _ => diskBarrier_smooth) (fun _ => baseBarrier_smooth L) df diskBarrier_escapes
    (baseBarrier_escapes hL) (fun _ => diskBarrier_nonneg) gap dJ JJ velocity
  intro p hp hr
  apply (base p hp (lt_of_le_of_lt (le_max_left _ _) hr)).congr
  have hi := (lt_div_iff₀ (by positivity : 0 < 4*L)).mp (hcut p.1
    ((le_max_right _ _).trans_lt hr) hp.1)
  have cont : Continuous (fun y : DiskProduct => 4 * L * b₀ y.1) :=
    continuous_const.mul (smooth_b₀.continuous.comp continuous_fst)
  filter_upwards [cont.continuousAt.eventually_lt_const (show 4 * L * b₀ p.1 < 1 by linarith)] with y hy
  simp [baseBarrier, extended_eq hy.le, sub_eq_add_neg]

end TransportOkaGrauert.CollarGluing
