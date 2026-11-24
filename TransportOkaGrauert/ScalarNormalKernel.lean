import TransportOkaGrauert.ScalarNormalEnergy
import Mathlib.Algebra.Order.ToIntervalMod

/-! # The nullspace of the scalar normal quadratic form -/
noncomputable section
namespace TransportOkaGrauert.ScalarRayPairing
open SimpleDiskTarget JacobiEnlargement GeodesicFlowExtension Complex MeasureTheory Set Metric Filter
open scoped ContDiff Topology Interval

variable {σ : ℂ → ℝ} (F : Flow σ)

theorem zero_of_nonnegative_integral {e : AngleTrace} (ce : Continuous e) (pe : period e)
    (pos : ∀ p, 0 ≤ e p) (zero : integral F e = 0) {p : State} (hp : ‖p.1‖ ≤ 1) : e p = 0 := by
  let pt := fun x : ScalarLiouville.BoxSpace => PolarCollar.direction (ScalarLiouville.point x)
  let G := fun x => Real.exp (2*F.factor (pt x).1) * e (pt x)
  have ct : Continuous pt := PolarCollar.direction.continuous.comp ScalarLiouville.point.continuous
  have cg : Continuous G := (continuous_const.mul (F.smoothFactor.continuous.comp (continuous_fst.comp ct))).rexp.mul (ce.comp ct)
  have ih : IntegrableOn G ScalarLiouville.box := cg.continuousOn.integrableOn_compact isCompact_Icc
  have ae := (integral_eq_zero_iff_of_nonneg (fun x => mul_nonneg (Real.exp_pos _).le (pos (pt x))) ih).mp zero
  let U : Set ScalarLiouville.BoxSpace := Set.pi univ (fun i => Ioo (ScalarLiouville.lo i) (ScalarLiouville.hi i))
  have ou : IsOpen U := isOpen_set_pi finite_univ (fun _ _ => isOpen_Ioo)
  have sub : U ⊆ ScalarLiouville.box := fun x hx => ⟨fun i => (hx i trivial).1.le,fun i => (hx i trivial).2.le⟩
  have eqU := Measure.eqOn_open_of_ae_eq (ae_restrict_of_ae_restrict_of_subset sub ae) ou cg.continuousOn continuousOn_const
  let v := fun t : ℝ => e (p.1,t)
  have cv : Continuous v := ce.comp (continuous_const.prodMk continuous_id)
  have open_eq : EqOn v (fun _ => 0) (Ioo (-Real.pi) Real.pi) := by
    intro t ht
    let x : ScalarLiouville.BoxSpace := ![p.1.re,p.1.im,t]
    have hRe := abs_le.mp ((Complex.abs_re_le_norm p.1).trans hp)
    have hIm := abs_le.mp ((Complex.abs_im_le_norm p.1).trans hp)
    have hx : x ∈ U := by
      intro i _
      fin_cases i
      · change -2 < p.1.re ∧ p.1.re < 2; constructor <;> linarith
      · change -2 < p.1.im ∧ p.1.im < 2; constructor <;> linarith
      · exact ht
    have eq := eqU hx
    change Real.exp (2*F.factor (pt x).1) * e (pt x) = 0 at eq
    have ep : pt x = (p.1,t) := by
      apply Prod.ext
      · change (ScalarLiouville.point x).1 = p.1
        apply Complex.ext <;> simp [x,ScalarLiouville.point_apply]
      · rfl
    have zz := (mul_eq_zero.mp eq).resolve_left (Real.exp_pos _).ne'
    rw [ep] at zz
    exact zz
  have closed_eq := open_eq.closure cv continuous_const
  rw [closure_Ioo (by linarith [Real.pi_pos] : -Real.pi ≠ Real.pi)] at closed_eq
  have periodic_v : Function.Periodic v (2*Real.pi) := fun t => by
    simpa [v,Prod.mk_add_mk] using pe (p.1,t)
  let a := toIocMod Real.two_pi_pos (-Real.pi) p.2
  let m := toIocDiv Real.two_pi_pos (-Real.pi) p.2
  have eq : a + m • (2*Real.pi) = p.2 := toIocMod_add_toIocDiv_zsmul Real.two_pi_pos _ _
  have ha : a ∈ Icc (-Real.pi) Real.pi := by
    have h := toIocMod_mem_Ioc Real.two_pi_pos (-Real.pi) p.2
    exact ⟨h.1.le,by dsimp [a]; linarith [h.2]⟩
  have e := (periodic_v.zsmul m) a
  rw [eq] at e
  exact e.trans (closed_eq ha)

theorem window_outside (W : Window F) (p : State) (hp : ‖p.1‖ ≤ 1) (t : ℝ)
    (h : t ≤ -W.T ∨ W.T ≤ t) : 1 < ‖F.base p t‖ := by
  by_contra! inside
  rcases h with h|h
  · have up : ‖F.base (F.val (p,t)) W.T‖ ≤ 1 := by
      rw [Flow.base,F.group]
      exact GeodesicNonreturn.stays_in_disk (F.geo p (Icc t 0)) inside
        (by simpa [Flow.base,F.initial] using hp) (fun q hq => F.convex q hq.le)
        (t+W.T) ⟨by linarith [W.pos],by linarith⟩
    exact (W.out _ inside).not_ge up
  · exact (W.out p hp).not_ge (F.stays le_rfl hp inside W.T ⟨W.pos.le,h⟩)

theorem ray_of_full {f : ℂ → ℝ} (hf : Continuous f) {r : ℝ} (hr₁ : r < 1)
    (off : ∀ z, r < ‖z‖ → f z = 0) (W : Window F)
    (null : ∀ q : State, ‖q.1‖ ≤ r → full F W (fun p => f p.1) q = 0)
    (p : State) (t : ℝ) (ht : 0 < t) (h0 : 1 < ‖p.1‖) (he : 1 < ‖F.base p t‖) :
    ScalarRayPrimitive.ray F f p t = 0 := by
  let g := fun s => f (F.base p s)
  by_cases hit : ∃ s ∈ Icc 0 t, ‖F.base p s‖ ≤ r
  · obtain ⟨s,hs,hq⟩ := hit
    let q := F.val (p,s)
    have iq : ‖q.1‖ ≤ 1 := hq.trans hr₁.le
    have past : ∀ a ≤ (0:ℝ), 1 < ‖F.base p a‖ :=
      (no_straddle F p h0).resolve_right (fun H => (H s hs.1).not_ge iq)
    have fut : ∀ a : ℝ, 0 ≤ a → 1 < ‖F.base (F.val (p,t)) a‖ := by
      apply (no_straddle F (F.val (p,t)) he).resolve_left
      intro H
      have h := H (s-t) (sub_nonpos.mpr hs.2)
      simp only [Flow.base,F.group,add_sub_cancel] at h
      exact h.not_ge iq
    have leftwin : (∫ a in 0..t, g a) = ∫ a, g a := by
      rw [intervalIntegral.integral_of_le ht.le]
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro a ha
      by_cases h : a ≤ 0
      · exact off _ (hr₁.trans (past a h))
      · have at' : t < a := lt_of_not_ge fun H => ha ⟨lt_of_not_ge h,H⟩
        have z := fut (a-t) (sub_nonneg.mpr at'.le)
        rw [Flow.base,F.group,add_sub_cancel] at z
        exact off _ (hr₁.trans z)
    have rightwin : (∫ a in -W.T+s..W.T+s, g a) = ∫ a, g a := by
      rw [intervalIntegral.integral_of_le (by linarith [W.pos])]
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro a ha
      have sep : a-s ≤ -W.T ∨ W.T ≤ a-s := by
        by_contra! q; exact ha ⟨by linarith [q.1],by linarith [q.2]⟩
      have h := window_outside F W q iq (a-s) sep
      simp only [q,Flow.base,F.group,add_sub_cancel] at h
      exact off _ (hr₁.trans h)
    have id : full F W (fun p => f p.1) q = ∫ a in -W.T+s..W.T+s, g a := by
      rw [full_eq F W (f := fun p => f p.1) (hf.comp continuous_fst)]
      have eq (a : ℝ) : f (F.val (q,a)).1 = g (a+s) := by simp [q,g,Flow.base,F.group,add_comm]
      simp only [eq]
      exact intervalIntegral.integral_comp_add_right g s
    exact leftwin.trans (rightwin.symm.trans (id.symm.trans (null q hq)))
  · change (∫ a in 0..t, g a) = 0
    calc
      _ = ∫ _a in 0..t, (0:ℝ) := intervalIntegral.integral_congr fun a ha =>
        off _ (lt_of_not_ge fun h => hit ⟨a,uIcc_of_le ht.le ▸ ha,h⟩)
      _ = 0 := intervalIntegral.integral_zero

/-- The actual normal quadratic form has trivial smooth compactly supported
kernel. -/
theorem zero_energy_injective (simple : SimpleMetric σ) (W : Window F) {r : ℝ}
    (hr : 0 ≤ r) (hr₁ : r < 1) {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f)
    (off : ∀ z, r < ‖z‖ → f z = 0)
    (null : integral F (fun p => f p.1 * full F W (fun q => f q.1) p) = 0) : f = 0 := by
  obtain ⟨w,sw,pw,_,nw,posw,sq⟩ := energy_square F W hr hr₁
  let g := fun p : State => f p.1
  have sg : ContDiff ℝ ∞ g := hf.comp contDiff_fst
  have pg : period g := fun p => by simp [g]
  have sq0 := (sq g sg pg (fun p => off p.1)).symm.trans null
  let A := full F W g
  have ca := (full_smooth F W sg).continuous
  have pa := full_period F W pg
  have ker (p : State) (hp : ‖p.1‖ ≤ r) : A p = 0 := by
    have pe : period (fun p => w p * A p ^ 2) := fun p => by
      simp only [pw p,show A (p+(0,2*Real.pi)) = A p from pa p]
    have z := zero_of_nonnegative_integral F (sw.continuous.mul (ca.pow 2)) pe
      (fun q => mul_nonneg (nw q) (sq_nonneg (A q))) sq0 (hp.trans hr₁.le)
    have zz := (mul_eq_zero.mp z).resolve_left (posw p hp).ne'
    nlinarith [sq_nonneg (A p)]
  exact ScalarPestov.scalar_ray_injective simple F hf (fun z h => off z (hr₁.trans h))
    (ray_of_full F hf.continuous hr₁ off W ker)

end TransportOkaGrauert.ScalarRayPairing
