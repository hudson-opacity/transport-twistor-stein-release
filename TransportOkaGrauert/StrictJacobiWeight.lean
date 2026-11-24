import TransportOkaGrauert.LeviBoundary
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# A strict Jacobi supersolution on a compact family of geodesics

The time coordinate is arclength from an entrance point outside the surface of
interest. At the evaluation times the ordinary scalar Jacobi field is positive.
One exponential perturbation of that field works on the entire compact family.
All the longitudinal derivatives below are ordinary real derivatives.
-/

noncomputable section

namespace TransportOkaGrauert.StrictJacobiWeight

open Filter Set
open scoped Topology ContDiff

/-- A field with a simple positive initial derivative and no later zeros stays
positive up to the evaluation time. In the geometric application the absence
of zeros is the no-conjugate-points property on the larger simple surface. -/
theorem positive_of_no_later_zeros {w : ℝ → ℝ} {T : ℝ} (hT : 0 < T)
    (h0 : w 0 = 0) (h1 : HasDerivWithinAt w 1 (Icc 0 T) 0) (hc : ContinuousOn w (Icc 0 T))
    (hn : ∀ t ∈ Ioc 0 T, w t ≠ 0) : 0 < w T := by
  have hslope : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t⁻¹ * w t := by
    have hr := (hasDerivWithinAt_iff_tendsto_slope' (by simp : (0 : ℝ) ∉ Ioo 0 T)).mp
      (h1.mono Ioo_subset_Icc_self)
    rw [nhdsWithin_Ioo_eq_nhdsGT hT] at hr
    simpa [slope_def_field, h0, div_eq_inv_mul] using hr.eventually (lt_mem_nhds zero_lt_one)
  have hnear : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < s := self_mem_nhdsWithin
  have hsmall : ∀ᶠ s in 𝓝[>] (0 : ℝ), s < T := nhdsWithin_le_nhds (gt_mem_nhds hT)
  obtain ⟨s, hs, hsT, hss⟩ := (hnear.and (hsmall.and hslope)).exists
  have hspos : 0 < s := hs
  have hsT' : s ≤ T := le_of_lt hsT
  have hws : 0 < w s := (mul_pos_iff_of_pos_left (inv_pos.mpr hspos)).mp hss
  by_contra! hbad
  have hc' := hc.mono (Icc_subset_Icc_left hspos.le)
  obtain ⟨t, ht, heq⟩ := intermediate_value_Icc' hsT' hc' ⟨hbad, hws.le⟩
  exact hn t ⟨hspos.trans_le ht.1, ht.2⟩ heq

/-- The perturbation uses the same two constants along every ray. -/
def weight (a d : ℝ) (w : ℝ → ℝ) (t : ℝ) : ℝ :=
  w t * (1 - d * Real.exp (a * t))

/-- The construction preserves the time regularity of the original field. -/
theorem weight_contDiffAt {n : WithTop ℕ∞} {w : ℝ → ℝ} {t : ℝ}
    (hw : ContDiffAt ℝ n w t) (a d : ℝ) : ContDiffAt ℝ n (weight a d w) t := by
  unfold weight
  fun_prop

private def bump (a d t : ℝ) : ℝ := d * Real.exp (a * t)

private theorem bump_hasDerivAt (a d t : ℝ) :
    HasDerivAt (bump a d) (a * bump a d t) t := by
  have he := (((hasDerivAt_id t).const_mul a).exp).const_mul d
  convert he using 1
  simp [bump]
  ring

private theorem weight_hasDerivAt {w : ℝ → ℝ} {t : ℝ}
    (hw : DifferentiableAt ℝ w t) (a d : ℝ) :
    HasDerivAt (weight a d w)
      (deriv w t * (1 - bump a d t) - w t * (a * bump a d t)) t := by
  convert hw.hasDerivAt.mul ((hasDerivAt_const t 1).sub (bump_hasDerivAt a d t)) using 1
  simp only [Pi.sub_apply]
  ring

/-- The product rule twice, without assuming the Jacobi equation. -/
theorem second_deriv_weight {w : ℝ → ℝ} {t : ℝ} (hw : ContDiffAt ℝ 2 w t) (a d : ℝ) :
    deriv (deriv (weight a d w)) t =
      deriv (deriv w) t * (1 - d * Real.exp (a * t)) -
        d * Real.exp (a * t) * a * (2 * deriv w t + a * w t) := by
  have hw₁ := hw.differentiableAt (by decide)
  have hw₂ := (hw.derivWithin (m := 1) (by decide)).differentiableAt (by decide)
  have he := bump_hasDerivAt a d t
  have hh := (hw₂.hasDerivAt.mul ((hasDerivAt_const t 1).sub he)).sub
    (hw₁.hasDerivAt.mul (he.const_mul a))
  have hloc := hh.congr_of_eventuallyEq (f₁ := deriv (weight a d w)) (by
    filter_upwards [hw.eventually (by decide)] with s hs
    exact (weight_hasDerivAt (hs.differentiableAt (by decide)) a d).deriv)
  rw [hloc.deriv]
  simp only [Pi.sub_apply, bump]
  ring

/-- The negative logarithm translates the Jacobi defect into the limiting
Schur complement. This is an identity of genuine first and second derivatives. -/
theorem negLog_schur_identity {y : ℝ → ℝ} {t : ℝ}
    (hy : ContDiffAt ℝ 2 y t) (hp : 0 < y t) (K : ℝ) :
    let h := fun s => -Real.log (y s)
    deriv (deriv h) t - K - (deriv h t) ^ 2 =
      -(deriv (deriv y) t + K * y t) / y t := by
  dsimp only
  have hy₁ := hy.differentiableAt (by decide)
  have hy₂ := (hy.derivWithin (m := 1) (by decide)).differentiableAt (by decide)
  have hfirst : HasDerivAt (fun s => -Real.log (y s)) (-(deriv y t / y t)) t :=
    (hy₁.hasDerivAt.log hp.ne').neg
  have hsecond := (hy₂.hasDerivAt.div hy₁.hasDerivAt hp.ne').neg
  have hnear := hy.continuousAt.eventually (lt_mem_nhds hp)
  have hloc := hsecond.congr_of_eventuallyEq (f₁ := deriv (fun s => -Real.log (y s))) (by
    filter_upwards [hy.eventually (by decide), hnear] with s hs hsp
    exact (((hs.differentiableAt (by decide)).hasDerivAt.log (ne_of_gt hsp)).neg).deriv)
  rw [hloc.deriv, hfirst.deriv]
  field_simp
  ring

/-- For a compact family of evaluation times, positive solutions of the
ordinary Jacobi equation give one positive strict supersolution with a uniform
positive relative defect. No variation of the curvature in the ODE is needed. -/
theorem exists_uniform_weight {P : Type*} [TopologicalSpace P] {S : Set P}
    (hS : IsCompact S) (τ K : P → ℝ) (w : P → ℝ → ℝ)
    (hτ : ContinuousOn τ S) (hc : ContinuousOn (fun p => w p (τ p)) S)
    (hc' : ContinuousOn (fun p => deriv (w p) (τ p)) S)
    (hw : ∀ p ∈ S, ContDiffAt ℝ 2 (w p) (τ p))
    (hp : ∀ p ∈ S, 0 < w p (τ p))
    (hode : ∀ p ∈ S, deriv (deriv (w p)) (τ p) + K p * w p (τ p) = 0) :
    ∃ a > 0, ∃ d > 0, ∃ ε > 0, ∀ p ∈ S,
      0 < weight a d (w p) (τ p) ∧
      deriv (deriv (weight a d (w p))) (τ p) + K p * weight a d (w p) (τ p)
        ≤ -ε * weight a d (w p) (τ p) := by
  let q (p : P) := -(2 * deriv (w p) (τ p)) / w p (τ p)
  have hq : ContinuousOn q S :=
    ((continuousOn_const.mul hc').neg).div hc (fun p h => (hp p h).ne')
  obtain ⟨C, hC⟩ := hS.bddAbove_image hq
  obtain ⟨T, hT⟩ := hS.bddAbove_image hτ
  let a := max C 0 + 1
  have ha : 0 < a := by dsimp [a]; linarith [le_max_right C 0]
  let d := (2 * Real.exp (a * T))⁻¹
  have hd : 0 < d := by dsimp [d]; positivity
  have hePos (p : P) : 0 < bump a d (τ p) := mul_pos hd (Real.exp_pos _)
  have heLt (p : P) (h : p ∈ S) : bump a d (τ p) < 1 := by
    have ht : τ p ≤ T := hT ⟨p, h, rfl⟩
    have hexp := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht ha.le)
    change (2 * Real.exp (a * T))⁻¹ * Real.exp (a * τ p) < 1
    rw [inv_mul_eq_div, div_lt_one (by positivity)]
    linarith [Real.exp_pos (a * T)]
  have hy (p : P) (h : p ∈ S) : 0 < weight a d (w p) (τ p) :=
    mul_pos (hp p h) (sub_pos.mpr (heLt p h))
  have hbracket (p : P) (h : p ∈ S) : 0 < 2 * deriv (w p) (τ p) + a * w p (τ p) := by
    have hcq : q p ≤ C := hC ⟨p, h, rfl⟩
    have hqa : q p < a := by dsimp [a]; linarith [le_max_left C 0]
    have hm := (div_lt_iff₀ (hp p h)).mp hqa
    linarith
  let ratio (p : P) := bump a d (τ p) * a * (2 * deriv (w p) (τ p) + a * w p (τ p)) /
    weight a d (w p) (τ p)
  have heCont : ContinuousOn (fun p => bump a d (τ p)) S :=
    continuousOn_const.mul (Real.continuous_exp.continuousOn.comp
      (continuousOn_const.mul hτ) (mapsTo_univ _ _))
  have hr : ContinuousOn ratio S :=
    (((heCont.mul continuousOn_const).mul
      ((continuousOn_const.mul hc').add (continuousOn_const.mul hc)))).div
      (hc.mul (continuousOn_const.sub heCont)) fun p h => (hy p h).ne'
  obtain ⟨ε, hε, hle⟩ := hS.exists_forall_le' hr (a := 0) (fun p h =>
    div_pos (mul_pos (mul_pos (hePos p) ha) (hbracket p h)) (hy p h))
  refine ⟨a, ha, d, hd, ε, hε, ?_⟩
  intro p h
  refine ⟨hy p h, ?_⟩
  have hrle := (le_div_iff₀ (hy p h)).mp (hle p h)
  rw [second_deriv_weight (hw p h)]
  dsimp only [weight, bump] at hrle ⊢
  nlinarith [congrArg (fun z : ℝ => z * (1 - d * Real.exp (a * τ p))) (hode p h)]

open LeviBoundary

/-- Continuity of the coefficients of the angular frame jet along the compact
direction family. The frame has no singular radial factors in these data. -/
structure ContinuousJetOn {P : Type*} [TopologicalSpace P] (j : P → FrameJet) (S : Set P) : Prop where
  curvature : ContinuousOn (fun p => (j p).curvature) S
  x : ContinuousOn (fun p => (j p).x) S
  h : ContinuousOn (fun p => (j p).h) S
  xx : ContinuousOn (fun p => (j p).xx) S
  hh : ContinuousOn (fun p => (j p).hh) S
  vv : ContinuousOn (fun p => (j p).vv) S
  hv : ContinuousOn (fun p => (j p).hv) S
  xv : ContinuousOn (fun p => (j p).xv) S

/-- One collar works for every direction in a compact set. Both the original
vertical Levi entry and its original Schur complement are strictly positive
throughout the collar. -/
theorem uniform_schur_collar {P : Type*} [TopologicalSpace P] {S : Set P}
    (hS : IsCompact S) (j : P → FrameJet) (hc : ContinuousJetOn j S)
    (hlim : ∀ p ∈ S, 0 < (j p).xx - (j p).curvature - (j p).x ^ 2) :
    ∃ η > 0, ∀ p ∈ S, ∀ t ∈ Ioo 0 η, 0 < vertical t (j p) ∧ 0 < schur t (j p) := by
  letI : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let good := {z : S × ℝ | 0 < vertical z.2 (j z.1) ∧ 0 < schur z.2 (j z.1)}
  have hlocal (p : S) : good ∈ 𝓝 p ×ˢ 𝓝[>] (0 : ℝ) := by
    let l := 𝓝 p ×ˢ 𝓝[>] (0 : ℝ)
    have ht : Tendsto Prod.snd l (𝓝 0) := tendsto_snd.mono_right nhdsWithin_le_nhds
    have htpos : ∀ᶠ z in l, 0 < z.2 := tendsto_snd.eventually
      (show ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t from self_mem_nhdsWithin)
    have hj (f : FrameJet → ℝ) (hf : ContinuousOn (fun p => f (j p)) S) :
        Tendsto (fun z : S × ℝ => f (j z.1)) l (𝓝 (f (j p))) :=
      hf.restrict.continuousAt.tendsto.comp tendsto_fst
    have hs := tendsto_schur (j := fun z : S × ℝ => j z.1) ht (htpos.mono fun _ h => h.ne')
      (hj _ hc.curvature) (hj _ hc.x) (hj _ hc.h) (hj _ hc.xx) (hj _ hc.hh)
      (hj _ hc.vv) (hj _ hc.hv) (hj _ hc.xv)
    have hb : Tendsto (fun z : S × ℝ => scaledVertical z.2 (j z.1)) l (𝓝 1) := by
      simpa [scaledVertical] using
        ((tendsto_const_nhds (x := (1 : ℝ))).sub (ht.pow 2)).add ((ht.pow 2).mul (hj _ hc.vv))
    filter_upwards [htpos, hb.eventually (lt_mem_nhds zero_lt_one),
      hs.eventually (lt_mem_nhds (hlim p p.property))] with z htpos hbpos hspos
    refine ⟨?_, hspos⟩
    have hid : scaledVertical z.2 (j z.1) = z.2 ^ 2 * vertical z.2 (j z.1) := by
      unfold scaledVertical vertical
      field_simp [htpos.ne']
    apply (mul_pos_iff_of_pos_left (sq_pos_of_pos htpos)).mp
    rwa [← hid]
  have hu := isCompact_univ.mem_nhdsSet_prod_of_forall
    (K := (univ : Set S)) (s := good) (fun p _ => hlocal p)
  obtain ⟨u, hu, v, hv, huv⟩ := Filter.mem_prod_iff.mp hu
  obtain ⟨η, hη, hv'⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hv
  exact ⟨η, hη, fun p hp t ht =>
    huv (show (⟨p, hp⟩, t) ∈ u ×ˢ v from
      ⟨subset_of_mem_nhdsSet hu (mem_univ _), hv' ht⟩)⟩

/-- The frame entries along the flow are derivatives of the negative logarithm
of the strict weight. A negative Jacobi defect supplies the positive boundary
limit needed for the common collar. -/
theorem uniform_collar_of_jacobi_defect {P : Type*} [TopologicalSpace P] {S : Set P}
    (hS : IsCompact S) (τ : P → ℝ) (y : P → ℝ → ℝ)
    (j : P → FrameJet) (hc : ContinuousJetOn j S)
    (hy : ∀ p ∈ S, ContDiffAt ℝ 2 (y p) (τ p)) (hp : ∀ p ∈ S, 0 < y p (τ p))
    (hode : ∀ p ∈ S, deriv (deriv (y p)) (τ p) + (j p).curvature * y p (τ p) < 0)
    (hx : ∀ p ∈ S, (j p).x = deriv (fun s => -Real.log (y p s)) (τ p))
    (hxx : ∀ p ∈ S, (j p).xx = deriv (deriv (fun s => -Real.log (y p s))) (τ p)) :
    ∃ η > 0, ∀ p ∈ S, ∀ t ∈ Ioo 0 η, 0 < vertical t (j p) ∧ 0 < schur t (j p) := by
  apply uniform_schur_collar hS j hc
  intro p hs
  rw [hx p hs, hxx p hs, negLog_schur_identity (hy p hs) (hp p hs)]
  exact div_pos (neg_pos.mpr (hode p hs)) (hp p hs)

/-- Along a flow segment the entrance datum does not change and arclength
increases by the flow parameter. These two local identities identify both
flow derivatives of the global angular weight with its time derivatives. -/
theorem flow_schur_identity {P G : Type*} (entry : P → G) (τ : P → ℝ)
    (w : G → ℝ → ℝ) (φ : ℝ → P) (p : P) (a d K : ℝ)
    (he : ∀ᶠ s in 𝓝 (0 : ℝ), entry (φ s) = entry p)
    (hτ : ∀ᶠ s in 𝓝 (0 : ℝ), τ (φ s) = τ p + s)
    (hw : ContDiffAt ℝ 2 (w (entry p)) (τ p))
    (hp : 0 < weight a d (w (entry p)) (τ p)) :
    let h := fun q => -Real.log (weight a d (w (entry q)) (τ q))
    deriv (deriv (h ∘ φ)) 0 - K - (deriv (h ∘ φ) 0) ^ 2 =
      -(deriv (deriv (weight a d (w (entry p)))) (τ p) +
        K * weight a d (w (entry p)) (τ p)) / weight a d (w (entry p)) (τ p) := by
  dsimp only
  let g := fun t => -Real.log (weight a d (w (entry p)) t)
  have hg : (fun q => -Real.log (weight a d (w (entry q)) (τ q))) ∘ φ =ᶠ[𝓝 0]
      (fun s => g (τ p + s)) := by
    filter_upwards [he, hτ] with s hs ht
    simp [hs, ht, g]
  rw [hg.deriv_eq, hg.deriv.deriv_eq]
  have hshift : deriv (fun s => g (τ p + s)) = fun s => deriv g (τ p + s) :=
    funext (deriv_comp_const_add g (τ p))
  rw [hshift, deriv_comp_const_add, add_zero]
  simpa only [add_zero] using negLog_schur_identity (weight_contDiffAt hw a d) hp K

/-- From the initial values, no second Jacobi zero, smooth longitudinal data,
and the entrance-time flow law, construct a single global angular weight for
the entire compact family. Its longitudinal Schur limit is uniformly positive.
Any continuous family of Levi jets with these longitudinal derivatives and
curvature has positive vertical entry and Schur complement in a common collar. -/
theorem exists_flow_weight_and_collar {P G : Type*} [TopologicalSpace P] {S : Set P}
    (hS : IsCompact S) (entry : P → G) (τ K : P → ℝ) (w : G → ℝ → ℝ)
    (φ : P → ℝ → P) (hτ : ContinuousOn τ S)
    (hc : ContinuousOn (fun p => w (entry p) (τ p)) S)
    (hc' : ContinuousOn (fun p => deriv (w (entry p)) (τ p)) S)
    (hw : ∀ p ∈ S, ContDiffAt ℝ 2 (w (entry p)) (τ p))
    (henter : ∀ p ∈ S, 0 < τ p ∧ w (entry p) 0 = 0 ∧ HasDerivWithinAt (w (entry p)) 1 (Icc 0 (τ p)) 0 ∧
      ContinuousOn (w (entry p)) (Icc 0 (τ p)) ∧
      ∀ t ∈ Ioc 0 (τ p), w (entry p) t ≠ 0)
    (hode : ∀ p ∈ S, deriv (deriv (w (entry p))) (τ p) + K p * w (entry p) (τ p) = 0)
    (hflow : ∀ p ∈ S, ∀ᶠ s in 𝓝 (0 : ℝ),
      entry (φ p s) = entry p ∧ τ (φ p s) = τ p + s) :
    ∃ a > 0, ∃ d > 0, ∃ ε > 0,
      let y := fun p => weight a d (w (entry p)) (τ p)
      let h := fun p => -Real.log (y p)
      (∀ p ∈ S, 0 < y p ∧ ε ≤ deriv (deriv (h ∘ φ p)) 0 - K p - (deriv (h ∘ φ p) 0) ^ 2) ∧
      (∀ j : P → FrameJet, ContinuousJetOn j S →
        (∀ p ∈ S, (j p).curvature = K p ∧ (j p).x = deriv (h ∘ φ p) 0 ∧
          (j p).xx = deriv (deriv (h ∘ φ p)) 0) →
        ∃ η > 0, ∀ p ∈ S, ∀ t ∈ Ioo 0 η, 0 < vertical t (j p) ∧ 0 < schur t (j p)) := by
  have hp (p : P) (hs : p ∈ S) : 0 < w (entry p) (τ p) := by
    obtain ⟨hpos, hzero, hd, hc, hn⟩ := henter p hs
    exact positive_of_no_later_zeros hpos hzero hd hc hn
  obtain ⟨a, ha, d, hd, ε, hε, hweight⟩ :=
    exists_uniform_weight hS τ K (fun p => w (entry p)) hτ hc hc' hw hp hode
  refine ⟨a, ha, d, hd, ε, hε, ?_⟩
  let y := fun p => weight a d (w (entry p)) (τ p)
  let h := fun p => -Real.log (y p)
  have hlim (p : P) (hs : p ∈ S) :
      ε ≤ deriv (deriv (h ∘ φ p)) 0 - K p - (deriv (h ∘ φ p) 0) ^ 2 := by
    obtain ⟨hy, hdef⟩ := hweight p hs
    rw [show deriv (deriv (h ∘ φ p)) 0 - K p - (deriv (h ∘ φ p) 0) ^ 2 = _ from
      flow_schur_identity entry τ w (φ p) p a d (K p)
        ((hflow p hs).mono fun _ e => e.1) ((hflow p hs).mono fun _ e => e.2) (hw p hs) hy]
    apply (le_div_iff₀ hy).mpr
    linarith
  refine ⟨fun p hs => ⟨(hweight p hs).1, hlim p hs⟩, ?_⟩
  intro j hj hjet
  apply uniform_schur_collar hS j hj
  intro p hs
  obtain ⟨hk, hx, hxx⟩ := hjet p hs
  rw [hk, hx, hxx]
  exact hε.trans_le (hlim p hs)

end TransportOkaGrauert.StrictJacobiWeight
