import TransportOkaGrauert.JacobiEnlargement

/-! # Smooth transverse entrance coordinates on the enlarged disk

For every point strictly inside a convex level circle, its negative-time
orbit meets that circle once. At the hit its radial velocity is nonzero;
the implicit function theorem makes the hit time jointly smooth. -/

noncomputable section
namespace TransportOkaGrauert.JacobiEnlargement.Flow

open Set Metric Filter Complex GeodesicFlowExtension SimpleRadialExit
open scoped ContDiff Topology

variable {σ : ℂ → ℝ} (F : JacobiEnlargement.Flow σ)

private theorem stays_interval {p : State} {a b R : ℝ} (hR : 1 ≤ R)
    (ha : ‖F.base p a‖ ≤ R) (hb : ‖F.base p b‖ ≤ R) :
    ∀ t ∈ Icc a b, ‖F.base p t‖ ≤ R :=
  GeodesicNonreturn.stays_in_disk (F.geo p _) ha hb (fun z hz => F.convex z (hR.trans hz.le))

private theorem hit_deriv {p : State} {a R : ℝ} (hR : 1 ≤ R) (ha : a < 0)
    (hp : ‖p.1‖ < R) (hit : ‖F.base p a‖ = R) :
    let v := 2 * Real.exp (-F.factor (F.base p a)) * normal (F.base p a) (Circle.exp (F.angle p a))
    HasDerivAt (fun t => normSq (F.base p t)) v a ∧ v ≠ 0 := by
  let z := F.base p
  let θ := F.angle p
  let N := fun s => normal (z s) (Circle.exp (θ s))
  let ρ := fun s => normSq (z s)
  have ray := F.geo p univ
  have dρ (t : ℝ) := radiusSq_deriv ray (univ_mem : univ ∈ 𝓝 t)
  refine ⟨dρ a,?_⟩
  intro zero
  have tan : N a = 0 := (mul_eq_zero.mp zero).resolve_left (by positivity)
  have dn := normal_deriv_at_tangent ray (univ_mem : univ ∈ 𝓝 a) tan
  have hcv := F.convex (z a) (hR.trans hit.ge)
  have slopePos := (hasDerivAt_iff_tendsto_slope_left_right.mp dn).2.eventually
    (Ioi_mem_nhds (mul_pos (Real.exp_pos _) hcv))
  have right : ∀ᶠ u in 𝓝[>] a, 0 < N u := by
    filter_upwards [slopePos,self_mem_nhdsWithin] with u hu hut
    change a < u at hut
    change 0 < slope N a u at hu
    rw [slope_def_field,tan,sub_zero] at hu
    exact (div_pos_iff_of_pos_right (sub_pos.mpr hut)).mp hu
  obtain ⟨v,hv,hsub⟩ := (mem_nhdsGT_iff_exists_mem_Ioc_Ioo_subset ha).mp right
  have hc : Continuous ρ := continuous_normSq.comp
    (continuous_fst.comp (F.smooth.continuous.comp (continuous_const.prodMk continuous_id)))
  obtain ⟨s,hs,eq⟩ := exists_hasDerivAt_eq_slope ρ _ hv.1 hc.continuousOn (fun t _ => dρ t)
  have inside := F.stays_interval hR hit.le
    (show ‖F.base p 0‖ ≤ R by simpa [base,F.initial] using hp.le) v ⟨hv.1.le,hv.2⟩
  have lo : ρ v ≤ ρ a := by
    rw [show ρ v = ‖F.base p v‖^2 from Complex.normSq_eq_norm_sq _,show ρ a = ‖F.base p a‖^2 from Complex.normSq_eq_norm_sq _,hit]
    exact pow_le_pow_left₀ (norm_nonneg _) inside 2
  have pos := mul_pos (mul_pos (by norm_num : (0:ℝ) < 2) (Real.exp_pos (-F.factor (z s)))) (hsub hs)
  exact (not_lt_of_ge (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr lo) (sub_nonneg.mpr hv.1.le))) (eq ▸ pos)

private theorem ordered_hits_false {p : State} {a b R : ℝ} (hR : 1 ≤ R) (hp : ‖p.1‖ < R)
    (hab : a < b) (hb : b < 0) (h₁ : ‖F.base p a‖ = R) (h₂ : ‖F.base p b‖ = R) : False := by
  have inner := F.stays_interval hR h₁.le (show ‖F.base p 0‖ ≤ R by simpa [base,F.initial] using hp.le)
  have localMax : IsLocalMax (fun s => normSq (F.base p s)) b := by
    filter_upwards [Icc_mem_nhds hab hb] with s hs
    change normSq (F.base p s) ≤ normSq (F.base p b)
    simp only [Complex.normSq_eq_norm_sq,h₂]
    exact pow_le_pow_left₀ (norm_nonneg _) (inner s hs) 2
  obtain ⟨d,n⟩ := F.hit_deriv hR hb hp h₂
  exact n (localMax.hasDerivAt_eq_zero d)

theorem unique_entrance {T R : ℝ} (hR : 1 ≤ R) (hT : 0 < T)
    (escape : ∀ p : State, ‖p.1‖ ≤ R → R < ‖F.base p T‖) {p : State} (hp : ‖p.1‖ < R) :
    ∃! a : ℝ, a < 0 ∧ ‖F.base p a‖ = R := by
  have back : R < ‖F.base p (-T)‖ := by
    by_contra! lock
    have h := escape (F.val (p,-T)) lock
    simp [base,F.group,F.initial,not_lt_of_ge hp.le] at h
  have at0 : ‖F.base p 0‖ < R := by simpa [base,F.initial] using hp
  have cont : Continuous (fun s => ‖F.base p s‖) := (continuous_fst.comp
    (F.smooth.continuous.comp (continuous_const.prodMk continuous_id))).norm
  obtain ⟨a,ha,eq⟩ := intermediate_value_Icc' (neg_nonpos.mpr hT.le) cont.continuousOn ⟨at0.le,back.le⟩
  have neg : a < 0 := ha.2.lt_of_ne (fun e => (eq ▸ (e ▸ at0).ne) rfl)
  refine ⟨a,⟨neg,eq⟩,?_⟩
  intro b hb
  rcases lt_trichotomy b a with h|h|h
  · exact (F.ordered_hits_false hR hp h neg hb.2 eq).elim
  · exact h
  · exact (F.ordered_hits_false hR hp h hb.1 eq hb.2).elim

open Classical in
private def chooseEntrance (radius : ℝ → ℝ) (R : ℝ) : ℝ :=
  if ex : ∃ a : ℝ, a < 0 ∧ radius a = R then Classical.choose ex else 0

/-- Signed entrance time, negative inside the disk, with a total ambient
representative for differentiating it as an ordinary real-valued function. -/
def entranceTime (R : ℝ) (p : State) : ℝ := chooseEntrance (fun s => ‖F.base p s‖) R

theorem entrance_shift (R : ℝ) (p : State) {a : ℝ} (ha : Circle.exp a = 1) :
    F.entranceTime R (p+(0,a)) = F.entranceTime R p := by
  apply congrArg (fun rad => chooseEntrance rad R)
  funext t
  simp [base,F.periodic p a ha]

theorem entrance_spec {T R : ℝ} (hR : 1 ≤ R) (hT : 0 < T)
    (escape : ∀ p : State, ‖p.1‖ ≤ R → R < ‖F.base p T‖) {p : State} (hp : ‖p.1‖ < R) :
    F.entranceTime R p < 0 ∧ ‖F.base p (F.entranceTime R p)‖ = R := by
  have ex := (F.unique_entrance hR hT escape hp).exists
  simpa only [entranceTime,chooseEntrance,dif_pos ex] using Classical.choose_spec ex

theorem entrance_smooth {T R : ℝ} (hR : 1 ≤ R) (hT : 0 < T)
    (escape : ∀ p : State, ‖p.1‖ ≤ R → R < ‖F.base p T‖) {p : State} (hp : ‖p.1‖ < R) :
    ContDiffAt ℝ ∞ (F.entranceTime R) p := by
  let a := F.entranceTime R p
  let H := fun u : State × ℝ => normSq (F.val u).1
  have sq : ContDiff ℝ ∞ normSq := by
    have eq : normSq = fun z : ℂ => z.re^2 + z.im^2 := by funext z; simp [Complex.normSq_apply,pow_two]
    rw [eq]; exact (reCLM.contDiff.pow 2).add (imCLM.contDiff.pow 2)
  have sm : ContDiff ℝ ∞ H := sq.comp (contDiff_fst.comp F.smooth)
  obtain ⟨ha,hit⟩ := F.entrance_spec hR hT escape hp
  obtain ⟨der,hn⟩ := F.hit_deriv hR ha hp hit
  have dH := (sm.differentiable (by simp) (p,a)).hasFDerivAt
  let inr := ContinuousLinearMap.inr ℝ State ℝ
  have incl : HasFDerivAt (fun s : ℝ => (p,s)) inr a :=
    (hasFDerivAt_const p a).prodMk (hasFDerivAt_id a)
  have eqD := (dH.comp a incl).unique der.hasFDerivAt
  have imp : IsContDiffImplicitAt ∞ H (fderiv ℝ H (p,a)) (p,a) := by
    refine ⟨dH,sm.contDiffAt,?_,by simp⟩
    change Function.Bijective ((fderiv ℝ H (p,a)).comp inr)
    rw [eqD]
    let v := 2 * Real.exp (-F.factor (F.base p a)) * normal (F.base p a) (Circle.exp (F.angle p a))
    exact ⟨fun u w e => (mul_right_cancel₀ hn e),fun w => ⟨w / v,div_mul_cancel₀ w hn⟩⟩
  have smi := imp.contDiffAt_implicitFunction
  have iv : imp.implicitFunction p = a := imp.eventually_implicitFunction_apply_eq.self_of_nhds rfl
  apply smi.congr_of_eventuallyEq
  filter_upwards [imp.apply_implicitFunction, smi.continuousAt.eventually_lt_const (show imp.implicitFunction p < 0 by rw [iv]; exact ha),
    continuous_fst.norm.continuousAt.eventually_lt_const hp] with q h h' hq
  apply (F.unique_entrance hR hT escape hq).unique (F.entrance_spec hR hT escape hq)
  refine ⟨h',?_⟩
  change normSq (F.base q _) = normSq (F.base p a) at h
  change ‖F.base p a‖ = R at hit
  simp only [Complex.normSq_eq_norm_sq,hit] at h
  nlinarith [norm_nonneg (F.base q (imp.implicitFunction q))]

/-- The entrance advances by minus elapsed flow time, and therefore the
physical entrance state is locally constant along the flow. -/
theorem entrance_advance {T R : ℝ} (hR : 1 ≤ R) (hT : 0 < T)
    (escape : ∀ p : State, ‖p.1‖ ≤ R → R < ‖F.base p T‖) {p : State} (hp : ‖p.1‖ < R) :
    ∀ᶠ s in 𝓝 0, F.entranceTime R (F.val (p,s)) = F.entranceTime R p - s ∧
      F.val (F.val (p,s), F.entranceTime R (F.val (p,s))) = F.val (p,F.entranceTime R p) := by
  obtain ⟨ha,hit⟩ := F.entrance_spec hR hT escape hp
  have cond : Continuous (fun t => ‖F.base p t‖) := (continuous_fst.comp
    (F.smooth.continuous.comp (continuous_const.prodMk continuous_id))).norm
  filter_upwards [Ioi_mem_nhds ha,cond.continuousAt.eventually_lt_const (by simpa [base,F.initial] using hp :
    ‖F.base p 0‖ < R)] with s hs hq
  have e : s + (F.entranceTime R p - s) = F.entranceTime R p := by ring
  have good := (F.unique_entrance hR hT escape hq).unique (F.entrance_spec hR hT escape hq)
    ⟨sub_neg.mpr hs,by simpa only [base,F.group,e] using hit⟩
  exact ⟨good,by rw [good,F.group,e]⟩

theorem entrance_periodic {T R : ℝ} (hR : 1 ≤ R) (hT : 0 < T)
    (escape : ∀ p : State, ‖p.1‖ ≤ R → R < ‖F.base p T‖) {p : State} (hp : ‖p.1‖ < R)
    {a : ℝ} (ha : Circle.exp a = 1) : F.entranceTime R (p+(0,a)) = F.entranceTime R p := by
  have hq : ‖(p+((0,a):State)).1‖ < R := by simpa using hp
  obtain ⟨neg,hit⟩ := F.entrance_spec hR hT escape hp
  exact (F.unique_entrance hR hT escape hq).unique (F.entrance_spec hR hT escape hq)
    ⟨neg,by simpa [base,F.periodic p a ha] using hit⟩

theorem entrance_bounded {T R : ℝ} (hR : 1 ≤ R) (hT : 0 < T)
    (escape : ∀ p : State, ‖p.1‖ ≤ R → R < ‖F.base p T‖) {p : State} (hp : ‖p.1‖ < R) :
    -F.entranceTime R p ∈ Ioo 0 T := by
  obtain ⟨ha,hit⟩ := F.entrance_spec hR hT escape hp
  refine ⟨neg_pos.mpr ha,?_⟩
  by_contra! h
  have inner := F.stays_interval hR hit.le
    (show ‖F.base p 0‖ ≤ R by simpa [base,F.initial] using hp.le) (-T)
    ⟨by linarith,neg_nonpos.mpr hT.le⟩
  have e := escape (F.val (p,-T)) inner
  simp [base,F.group,F.initial,not_lt_of_ge hp.le] at e

end TransportOkaGrauert.JacobiEnlargement.Flow
