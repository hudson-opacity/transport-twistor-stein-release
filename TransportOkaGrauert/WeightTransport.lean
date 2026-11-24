import TransportOkaGrauert.RayTests
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Tactic

/-!
# Stability of normalized transport weights on a ray

The weight convention is right multiplication, W' = W A, with W(a) = 1.
All coefficient and solution assumptions are restricted to the closed ray
interval. The ambient algebra may in particular be a matrix or operator algebra.
-/
noncomputable section
namespace TransportOkaGrauert.WeightTransport

open Set MeasureTheory
open scoped Topology

variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R]
variable {A B W V : ℝ → R} {a b K ε : ℝ}

/-- Normalized inverse parallel transport for the coefficient along one ray. -/
structure IsWeight (A W : ℝ → R) (a b : ℝ) : Prop where
  initial : W a = 1
  deriv : ∀ t ∈ Icc a b, HasDerivWithinAt W (W t * A t) (Icc a b) t

/-- Equivalent integral equation, including the endpoints. -/
theorem isWeight_iff_integral [CompleteSpace R] (hab : a ≤ b) (hA : ContinuousOn A (Icc a b)) :
    IsWeight A W a b ↔ ContinuousOn W (Icc a b) ∧
      ∀ t ∈ Icc a b, W t = 1 + ∫ u in a..t, W u * A u := by
  constructor
  · intro h
    have hc := HasDerivWithinAt.continuousOn h.deriv
    refine ⟨hc, fun t ht => ?_⟩
    have sub := Icc_subset_Icc_right (a := a) ht.2
    have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1 (hc.mono sub)
      (fun u (hu : u ∈ Ioo a t) => (h.deriv u (sub (Ioo_subset_Icc_self hu))).hasDerivAt
        (Icc_mem_nhds hu.1 (hu.2.trans_le ht.2)))
      (((hc.mul hA).mono (uIcc_of_le ht.1 ▸ sub)).intervalIntegrable)
    rw [hi, h.initial]
    abel
  · rintro ⟨hc, he⟩
    refine ⟨by simpa using he a ⟨le_rfl, hab⟩, fun t ht => ?_⟩
    haveI : Fact (t ∈ Icc a b) := ⟨ht⟩
    have hWA := hc.mul hA
    have hi : IntervalIntegrable (fun u => W u * A u) volume a t :=
      (hWA.mono (uIcc_of_le ht.1 ▸ Icc_subset_Icc_right ht.2)).intervalIntegrable
    exact ((intervalIntegral.integral_hasDerivWithinAt_right hi
      (hWA.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t)
      (hWA t ht)).const_add (1 : R)).congr_of_mem he ht

private theorem deriv_right (h : IsWeight A W a b) {t : ℝ} (ht : t ∈ Ico a b) :
    HasDerivWithinAt W (W t * A t) (Ici t) t :=
  (h.deriv t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)

/-- Growth from normalization for a bounded coefficient. -/
theorem IsWeight.norm_le (h : IsWeight A W a b) (hK : ∀ t ∈ Ico a b, ‖A t‖ ≤ K)
    {t : ℝ} (ht : t ∈ Icc a b) : ‖W t‖ ≤ ‖(1 : R)‖ * Real.exp (K * (t - a)) := by
  have hg := norm_le_gronwallBound_of_norm_deriv_right_le
    (HasDerivWithinAt.continuousOn h.deriv) (fun _ hx => deriv_right h hx)
    (le_of_eq (congrArg norm h.initial)) (K := K) (ε := 0) (fun u hu => by
      rw [add_zero, mul_comm]
      exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (hK u hu) (norm_nonneg _))) t ht
  simpa only [gronwallBound_ε0] using hg

/-- Time response of the inhomogeneous Grönwall bound, continuous also at
zero coefficient. The zero branch contains the length of the interval. -/
def response (K T : ℝ) : ℝ := if K = 0 then T else (Real.exp (K*T) - 1) / K

private theorem gronwall_zero_initial (K x T : ℝ) :
    gronwallBound 0 K x T = x * response K T := by
  by_cases hK : K = 0
  · simp [gronwallBound, response, hK]
  · simp only [gronwallBound, response, hK, if_false, zero_mul, zero_add]
    ring

/-- A coefficient perturbation estimate uniform over the whole ray. When the
reference weight is unitary one can take its norm bound M to be one. -/
theorem IsWeight.sub_norm_le_of_bound (hW : IsWeight A W a b) (hV : IsWeight B V a b)
    (hK : 0 ≤ K) (hε : 0 ≤ ε) {M : ℝ} (hM : 0 ≤ M)
    (hA : ∀ t ∈ Ico a b, ‖A t‖ ≤ K) (hVbound : ∀ t ∈ Ico a b, ‖V t‖ ≤ M)
    (hAB : ∀ t ∈ Ico a b, ‖A t - B t‖ ≤ ε) {t : ℝ} (ht : t ∈ Icc a b) :
    ‖W t - V t‖ ≤ ε * (M * response K (b-a)) := by
  let D := fun u => W u - V u
  have hc : ContinuousOn D (Icc a b) :=
    (HasDerivWithinAt.continuousOn hW.deriv).sub (HasDerivWithinAt.continuousOn hV.deriv)
  have bound (u : ℝ) (hu : u ∈ Ico a b) :
      ‖W u * A u - V u * B u‖ ≤ K * ‖D u‖ + M * ε := by
    rw [show W u * A u - V u * B u = D u * A u + V u * (A u - B u) by dsimp [D]; noncomm_ring]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [mul_comm K]
      exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (hA u hu) (norm_nonneg _))
    · exact (norm_mul_le _ _).trans (mul_le_mul (hVbound u hu) (hAB u hu) (norm_nonneg _) hM)
  have hg := norm_le_gronwallBound_of_norm_deriv_right_le (δ := 0) hc
    (fun _ hu => (deriv_right hW hu).sub (deriv_right hV hu))
    (by simp [D, hW.initial, hV.initial]) bound t ht
  apply hg.trans
  calc
    gronwallBound 0 K (M * ε) (t - a) ≤ gronwallBound 0 K (M * ε) (b - a) :=
      gronwallBound_mono (le_refl _) (mul_nonneg hM hε) hK (sub_le_sub_right ht.2 _)
    _ = ε * (M * response K (b-a)) := by rw [gronwall_zero_initial]; ring

/-- Uniform dependence involving only coefficient bounds and ray length.
It applies to any number of rays sharing these bounds. -/
theorem IsWeight.sub_norm_le (hW : IsWeight A W a b) (hV : IsWeight B V a b)
    (hK : 0 ≤ K) (hε : 0 ≤ ε) (hA : ∀ t ∈ Ico a b, ‖A t‖ ≤ K)
    (hB : ∀ t ∈ Ico a b, ‖B t‖ ≤ K) (hAB : ∀ t ∈ Ico a b, ‖A t - B t‖ ≤ ε)
    {t : ℝ} (ht : t ∈ Icc a b) :
    ‖W t - V t‖ ≤ ε * ((‖(1 : R)‖ * Real.exp (K*(b-a))) * response K (b-a)) := by
  apply hW.sub_norm_le_of_bound hV hK hε (by positivity) hA _ hAB ht
  intro u hu
  exact (hV.norm_le hB (Ico_subset_Icc_self hu)).trans (by
    gcongr
    exact hu.2.le)

/-- Concatenate two normalized evolutions by multiplying the second one on
the left by the terminal value of the first. The one-sided derivatives at
the joining point agree, including for a noncommutative coefficient algebra. -/
private theorem join {c : ℝ} (hac : a ≤ c) (hcb : c ≤ b)
    (hW : IsWeight A W a c) (hV : IsWeight A V c b) : ∃ Z, IsWeight A Z a b := by
  let Z := fun t => if t ≤ c then W t else W c * V t
  have left : EqOn Z W (Icc a c) := fun t ht => if_pos ht.2
  have right : EqOn Z (fun t => W c * V t) (Icc c b) := by
    intro t ht
    by_cases h : t ≤ c
    · have e := le_antisymm h ht.1
      simp [Z, e, hV.initial]
    · exact if_neg h
  have dl (t : ℝ) (ht : t ∈ Icc a c) : HasDerivWithinAt Z (Z t * A t) (Icc a c) t := by
    rw [left ht]
    exact (hW.deriv t ht).congr_of_mem (fun _ h => left h) ht
  have dr (t : ℝ) (ht : t ∈ Icc c b) : HasDerivWithinAt Z (Z t * A t) (Icc c b) t := by
    have hd : HasDerivWithinAt (fun u => W c * V u) ((W c * V t) * A t) (Icc c b) t := by
      simpa only [mul_assoc] using (hV.deriv t ht).const_mul (W c)
    rw [right ht]
    exact hd.congr_of_mem (fun _ h => right h) ht
  refine ⟨Z, left ⟨le_rfl, hac⟩ |>.trans hW.initial, fun t ht => ?_⟩
  rcases lt_trichotomy t c with h | rfl | h
  · apply (dl t ⟨ht.1, h.le⟩).mono_of_mem_nhdsWithin
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds h)] with u hu huc
    exact ⟨hu.1, huc.le⟩
  · simpa only [Icc_union_Icc_eq_Icc hac hcb] using
      (dl t ⟨hac, le_rfl⟩).union (dr t ⟨le_rfl, hcb⟩)
  · apply (dr t ⟨h.le, ht.2⟩).mono_of_mem_nhdsWithin
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds h)] with u hu hcu
    exact ⟨hcu.le, hu.2⟩

/-- Picard iteration on an interval with small coefficient norm times length. -/
private theorem exists_short [CompleteSpace R] (hab : a ≤ b)
    (hA : ContinuousOn A (Icc a b)) (K : NNReal) (bound : ∀ t ∈ Icc a b, ‖A t‖ ≤ K)
    (small : 2 * (K : ℝ) * (b-a) ≤ 1) : ∃ W, IsWeight A W a b := by
  let r : NNReal := ‖(1 : R)‖₊ + 1
  let t₀ : Icc a b := ⟨a, le_rfl, hab⟩
  have hp : IsPicardLindelof (fun t x => x * A t) t₀ (1 : R) r 0 (2*r*K) K := by
    constructor
    · intro t ht x _ y _
      rw [edist_nndist, edist_nndist, ← ENNReal.coe_mul, ENNReal.coe_le_coe]
      change dist (x * A t) (y * A t) ≤ (K : ℝ) * dist x y
      rw [dist_eq_norm, dist_eq_norm, ← sub_mul, mul_comm (K : ℝ)]
      exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (bound t ht) (norm_nonneg _))
    · intro x _
      exact continuousOn_const.mul hA
    · intro t ht x hx
      have hx' : ‖x - 1‖ ≤ (r : ℝ) := by simpa [Metric.mem_closedBall, dist_eq_norm] using hx
      have hr : ‖(1 : R)‖ ≤ (r : ℝ) := by simp [r]
      have hx'' : ‖x‖ ≤ 2 * (r : ℝ) := by
        have h := norm_add_le (x - 1) (1 : R)
        rw [sub_add_cancel] at h
        linarith
      exact (norm_mul_le _ _).trans (mul_le_mul hx'' (bound t ht) (norm_nonneg _) (mul_nonneg (by norm_num) r.2))
    · change ((2 : ℝ) * r * K) * max (b - a) (a-a) ≤ (r : ℝ) - 0
      rw [sub_self, max_eq_left (sub_nonneg.mpr hab), sub_zero]
      nlinarith [mul_le_mul_of_nonneg_left small (show 0 ≤ (r : ℝ) from r.2)]
  obtain ⟨W, h₀, hd⟩ := hp.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨W, h₀, hd⟩

/-- Every continuous coefficient on a compact ray has a normalized weight.
The proof joins local Picard solutions by finite dyadic subdivision. -/
theorem exists_weight [CompleteSpace R] (hab : a ≤ b) (hA : ContinuousOn A (Icc a b)) :
    ∃ W, IsWeight A W a b := by
  obtain ⟨s, _, hs⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hab) hA.norm
  let M := ‖A s‖₊
  have haux (n : ℕ) : ∀ x y : ℝ, x ≤ y → Icc x y ⊆ Icc a b →
      2 * (M : ℝ) * (y-x) ≤ (2:ℝ)^n → ∃ W, IsWeight A W x y := by
    induction n with
    | zero =>
      intro x y hxy hsub hsmall
      exact exists_short hxy (hA.mono hsub) M (fun _ h => hs (hsub h)) (by simpa using hsmall)
    | succ n ih =>
      intro x y hxy hsub hsmall
      let m := (x+y)/2
      have hxm : x ≤ m := by dsimp [m]; linarith
      have hmy : m ≤ y := by dsimp [m]; linarith
      rw [pow_succ] at hsmall
      obtain ⟨W, hw⟩ := ih x m hxm ((Icc_subset_Icc_right hmy).trans hsub) (by dsimp [m]; linarith)
      obtain ⟨V, hv⟩ := ih m y hmy ((Icc_subset_Icc_left hxm).trans hsub) (by dsimp [m]; linarith)
      exact join hxm hmy hw hv
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (2 * (M : ℝ) * (b-a)) (by norm_num : (1:ℝ) < 2)
  exact haux n a b hab Subset.rfl hn.le

/-- All normalized solutions for a continuous coefficient agree on the ray. -/
theorem IsWeight.eqOn (hW : IsWeight A W a b) (hV : IsWeight A V a b)
    (hA : ContinuousOn A (Icc a b)) : EqOn W V (Icc a b) := by
  intro t ht
  obtain ⟨s, _, hs⟩ := isCompact_Icc.exists_isMaxOn ⟨t, ht⟩ hA.norm
  have hK (u : ℝ) (hu : u ∈ Ico a b) : ‖A u‖ ≤ ‖A s‖ := hs (Ico_subset_Icc_self hu)
  have h := hW.sub_norm_le hV (norm_nonneg (A s)) (le_refl 0) hK hK (by simp) ht
  exact sub_eq_zero.mp (by simpa using h)

section CoefficientMap
variable [CompleteSpace R]

/-- Extend a path constantly at both ends for interval differentiation. -/
def along (hab : a ≤ b) (A : C(Icc a b, R)) (t : ℝ) : R :=
  A (projIcc a b hab t)

omit [NormedAlgebra ℝ R] [CompleteSpace R] in
private theorem along_continuous (hab : a ≤ b) (A : C(Icc a b, R)) :
    Continuous (along hab A) := A.continuous.comp continuous_projIcc

private def selected (hab : a ≤ b) (A : C(Icc a b, R)) :=
  Classical.choose (exists_weight hab (along_continuous hab A).continuousOn)

private theorem selected_spec (hab : a ≤ b) (A : C(Icc a b, R)) :
    IsWeight (along hab A) (selected hab A) a b :=
  Classical.choose_spec (exists_weight hab (along_continuous hab A).continuousOn)

/-- Normalized transport as a map from continuous coefficients to continuous
weights, both in their uniform norms on the fixed compact ray interval. -/
def weight (hab : a ≤ b) (A : C(Icc a b, R)) : C(Icc a b, R) :=
  ⟨fun t => selected hab A t, (HasDerivWithinAt.continuousOn (selected_spec hab A).deriv).restrict⟩

theorem weight_solves (hab : a ≤ b) (A : C(Icc a b,R)) :
    IsWeight (along hab A) (along hab (weight hab A)) a b := by
  have eqn (t : ℝ) (ht : t ∈ Icc a b) : along hab (weight hab A) t = selected hab A t := by
    simp [along, weight, projIcc_of_mem hab ht]
  have hs := selected_spec hab A
  refine ⟨(eqn a ⟨le_rfl, hab⟩).trans hs.initial, fun t ht => ?_⟩
  rw [eqn t ht]
  exact (hs.deriv t ht).congr_of_mem eqn ht

/-- A Lipschitz bound on each coefficient norm ball, in the uniform norms
on the entire coefficient and transport paths. -/
theorem weight_lipschitzOn (hab : a ≤ b) (K : NNReal) :
    ∃ L : NNReal, LipschitzOnWith L (weight (R := R) hab) (Metric.closedBall 0 K) := by
  let L := (‖(1 : R)‖ * Real.exp ((K:ℝ)*(b-a))) * response K (b-a)
  have hr : 0 ≤ response K (b-a) := by
    unfold response
    split_ifs
    · exact sub_nonneg.mpr hab
    · exact div_nonneg (sub_nonneg.mpr (Real.one_le_exp (mul_nonneg K.2 (sub_nonneg.mpr hab)))) K.2
  have hL : 0 ≤ L := mul_nonneg (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le) hr
  refine ⟨⟨L, hL⟩, LipschitzOnWith.of_dist_le_mul ?_⟩
  intro A hA B hB
  have ha : ‖A‖ ≤ K := by simpa [Metric.mem_closedBall] using hA
  have hb : ‖B‖ ≤ K := by simpa [Metric.mem_closedBall] using hB
  rw [dist_eq_norm, dist_eq_norm]
  apply (ContinuousMap.norm_le _ (mul_nonneg hL (norm_nonneg _))).mpr
  intro t
  have h := (selected_spec hab A).sub_norm_le (selected_spec hab B) K.2 (norm_nonneg (A-B))
    (fun u _ => (A.norm_coe_le_norm (projIcc a b hab u)).trans ha)
    (fun u _ => (B.norm_coe_le_norm (projIcc a b hab u)).trans hb)
    (fun u _ => (A-B).norm_coe_le_norm (projIcc a b hab u)) t.property
  exact h.trans_eq (mul_comm _ _)

/-- Uniform perturbations of the coefficient give uniform perturbations of
the normalized transport, at any bounded coefficient on a compact ray. -/
theorem weight_continuous (hab : a ≤ b) : Continuous (weight (R := R) hab) := by
  rw [continuous_iff_continuousAt]
  intro A
  let K : NNReal := ‖A‖₊ + 1
  obtain ⟨L, hL⟩ := weight_lipschitzOn (R := R) hab K
  have ha : dist A 0 < (K : ℝ) := by simp [K]
  exact (hL.continuousOn A (Metric.mem_closedBall.mpr ha.le)).continuousAt
    (Metric.closedBall_mem_nhds_of_mem (Metric.mem_ball.mpr ha))

/-- Pull a phase-space coefficient back to the ray with its actual length,
then solve on normalized time in the unit interval. -/
def rayWeight {P B : Type*} [TopologicalSpace P] [TopologicalSpace B]
    (g : RayTests.Geometry B P) (A : C(P,R)) (b : B) : C(RayTests.UnitSegment, R) :=
  weight zero_le_one ⟨fun t => g.length b • A (g.path (b,t)),
    continuous_const.smul (A.continuous.comp
      (g.path.continuous.comp (continuous_const.prodMk continuous_id)))⟩

/-- Joint continuity of the full transport path in the phase-space
coefficient (uniform norm) and the incoming ray label. -/
theorem rayWeight_continuous {P B : Type*} [TopologicalSpace P] [CompactSpace P]
    [TopologicalSpace B] (g : RayTests.Geometry B P) :
    Continuous (fun p : C(P,R) × B => rayWeight g p.1 p.2) := by
  apply (weight_continuous zero_le_one).comp
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : (C(P,R) × B) × RayTests.UnitSegment =>
    g.length p.1.2 • p.1.1 (g.path (p.1.2, p.2)))
  have hb : Continuous (fun p : (C(P,R) × B) × RayTests.UnitSegment => p.1.2) :=
    continuous_snd.comp continuous_fst
  exact (g.length.continuous.comp hb).smul <| continuous_eval.comp
    ((continuous_fst.comp continuous_fst).prodMk (g.path.continuous.comp (hb.prodMk continuous_snd)))

end CoefficientMap
end TransportOkaGrauert.WeightTransport
