import TransportOkaGrauert.ChartJacobi
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Smoothing a strict Jacobi weight in entrance coordinates

A frozen ray profile is an ordinary smooth function of arclength. The strict
inequalities on its entire compact entrance fibre persist on an open set of
nearby entrances. Smooth nonnegative cutoffs on finitely many such sets then
give a jointly smooth weight. Since the cutoffs only depend on entrance data,
no derivatives of cutoffs enter the longitudinal Jacobi inequality.
-/

noncomputable section

namespace TransportOkaGrauert.SmoothJacobiFamily

open Set Filter Metric ChartJacobi SimpleDiskTarget StrictJacobiWeight
open scoped Topology ContDiff

private theorem second_deriv_sum {ι : Type*} (I : Finset ι) (b : ι → ℝ) (f : ι → ℝ → ℝ)
    {U : Set ℝ} (hU : IsOpen U) (hf : ∀ i, ContDiffOn ℝ ∞ (f i) U)
    {t : ℝ} (ht : t ∈ U) :
    deriv (deriv (fun s => ∑ i ∈ I, b i * f i s)) t =
      ∑ i ∈ I, b i * deriv (deriv (f i)) t := by
  have hdiff (s : ℝ) (hs : s ∈ U) (i : ι) :=
    (hf i).contDiffAt (hU.mem_nhds hs)
  have hd (s : ℝ) (hs : s ∈ U) :
      deriv (fun r => ∑ i ∈ I, b i * f i r) s = ∑ i ∈ I, b i * deriv (f i) s :=
    (HasDerivAt.fun_sum fun i _ => ((hdiff s hs i).differentiableAt (by decide)).hasDerivAt.const_mul (b i)).deriv
  have he : deriv (fun r => ∑ i ∈ I, b i * f i r) =ᶠ[𝓝 t] fun s => ∑ i ∈ I, b i * deriv (f i) s := by
    filter_upwards [hU.mem_nhds ht] with s hs
    exact hd s hs
  rw [he.deriv_eq]
  exact (HasDerivAt.fun_sum fun i _ =>
    (((hdiff t ht i).derivWithin (m := 1) (by decide)).differentiableAt
      (by decide)).hasDerivAt.const_mul (b i)).deriv

/-- Local weights need only be smooth in time and work on each whole entrance
fibre. No regularity in the selection of these local weights is required. -/
theorem glue_frozen_profiles {P G : Type*} [TopologicalSpace P] [CompactSpace P]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    {U : Set ℝ} (hU : IsOpen U) (entry : P → G) (τ K : P → ℝ)
    (he : Continuous entry) (hτ : Continuous τ) (hk : Continuous K) (ht : ∀ p, τ p ∈ U)
    (hprofiles : ∀ p₀ : P, ∃ f : ℝ → ℝ, ContDiffOn ℝ ∞ f U ∧
      ∀ p : P, entry p = entry p₀ → 0 < f (τ p) ∧ deriv (deriv f) (τ p) + K p * f (τ p) < 0) :
    ∃ F : G × ℝ → ℝ, ContDiffOn ℝ ∞ F (univ ×ˢ U) ∧ ∀ p : P,
      0 < F (entry p, τ p) ∧
      deriv (deriv (fun s => F (entry p, s))) (τ p) + K p * F (entry p, τ p) < 0 := by
  classical
  choose f hf hpos using hprofiles
  let bad (i : P) := {p : P | 0 < f i (τ p) ∧
    deriv (deriv (f i)) (τ p) + K p * f i (τ p) < 0}ᶜ
  let O (i : P) := (entry '' bad i)ᶜ
  have hopen (i : P) : IsOpen (O i) := by
    have pull (v : ℝ → ℝ) (hv : ContinuousOn v U) : Continuous (fun p => v (τ p)) :=
      continuousOn_univ.mp (hv.comp hτ.continuousOn (fun p _ => ht p))
    have hv := pull (f i) (hf i).continuousOn
    have hss := ((hf i).deriv_of_isOpen hU (m := 1) (by decide)).deriv_of_isOpen hU
      (m := 0) (by decide)
    have hd := pull _ hss.continuousOn
    have hb : IsClosed (bad i) := ((isOpen_lt continuous_const hv).inter
      (isOpen_lt (hd.add (hk.mul hv)) continuous_const)).isClosed_compl
    exact (hb.isCompact.image he).isClosed.isOpen_compl
  have hcover : range entry ⊆ ⋃ i, O i := by
    rintro _ ⟨p, rfl⟩
    apply mem_iUnion.mpr
    refine ⟨p, ?_⟩
    rintro ⟨q, hbad, heq⟩
    exact hbad (hpos p q heq)
  obtain ⟨I, hI⟩ := (isCompact_range he).elim_finite_subcover O hopen hcover
  choose b hsupport hb hbounds using fun i => (hopen i).exists_contDiff_support_eq (n := ⊤)
  let F (u : G × ℝ) := ∑ i ∈ I, b i u.1 * f i u.2
  refine ⟨F, ?_, ?_⟩
  · apply ContDiffOn.sum
    intro i _
    exact ((hb i).comp contDiff_fst).contDiffOn.mul ((hf i).comp contDiffOn_snd fun _ h => h.2)
  intro p
  have hactive (i : P) (hi : b i (entry p) ≠ 0) :
      0 < f i (τ p) ∧ deriv (deriv (f i)) (τ p) + K p * f i (τ p) < 0 := by
    have hh : entry p ∈ O i := hsupport i ▸ (show entry p ∈ Function.support (b i) from hi)
    by_contra h
    exact hh ⟨p, h, rfl⟩
  obtain ⟨j, hjI, hjO⟩ := mem_iUnion₂.mp (hI (mem_range_self p))
  have hbj : b j (entry p) ≠ 0 := by
    change entry p ∈ Function.support (b j)
    rwa [hsupport]
  have hnonneg (i : P) : 0 ≤ b i (entry p) := (hbounds i (mem_range_self _)).1
  have hbjpos : 0 < b j (entry p) := lt_of_le_of_ne (hnonneg j) hbj.symm
  have weighted (v : P → ℝ) (hv : ∀ i, b i (entry p) ≠ 0 → 0 < v i) :
      0 < ∑ i ∈ I, b i (entry p) * v i := by
    apply Finset.sum_pos' _ ⟨j, hjI, mul_pos hbjpos (hv j hbj)⟩
    intro i _
    by_cases h : b i (entry p) = 0
    · simp [h]
    · exact mul_nonneg (hnonneg i) (hv i h).le
  refine ⟨weighted _ (fun i hi => (hactive i hi).1), ?_⟩
  change deriv (deriv (fun s => ∑ i ∈ I, b i (entry p) * f i s)) (τ p) +
    K p * (∑ i ∈ I, b i (entry p) * f i (τ p)) < 0
  rw [second_deriv_sum I _ f hU hf (ht p), Finset.mul_sum, ← Finset.sum_add_distrib]
  have hn := weighted (fun i => -(deriv (deriv (f i)) (τ p) + K p * f i (τ p)))
    (fun i hi => neg_pos.mpr (hactive i hi).2)
  rw [← neg_pos, ← Finset.sum_neg_distrib]
  convert hn using 1
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- A single normalized field is smooth in arclength on a smooth curvature
path. This uses the proved regularity theorem for integral curves of smooth
ODEs. It makes no assertion about parameter derivatives of an ODE solver. -/
theorem field_smoothOn {T : ℝ} (hT : 0 ≤ T) (κ : ℝ → ℝ)
    (hκ : ContDiffOn ℝ ∞ κ (Icc 0 T)) :
    let k : C(Icc 0 T, ℝ) := ⟨(Icc 0 T).restrict κ, hκ.continuousOn.restrict⟩
    ContDiffOn ℝ ∞ (field hT k) (Icc 0 T) := by
  dsimp only
  let k : C(Icc 0 T, ℝ) := ⟨(Icc 0 T).restrict κ, hκ.continuousOn.restrict⟩
  let f := fun t (x : ℝ × ℝ) => (x.2, -κ t * x.1)
  let α := fun t => (field hT k t, speed hT k t)
  have hf : ContDiffOn ℝ ∞ (Function.uncurry f) ((Icc 0 T) ×ˢ (univ : Set (ℝ × ℝ))) := by
    have hc := hκ.comp (contDiffOn_fst (s := (Icc 0 T) ×ˢ (univ : Set (ℝ × ℝ)))) (fun _ hp => hp.1)
    exact (contDiff_snd.comp contDiff_snd).contDiffOn.prodMk
      (hc.neg.mul ((contDiff_fst.comp contDiff_snd).contDiffOn))
  have hd (t : ℝ) (ht : t ∈ Icc 0 T) : HasDerivWithinAt α (f t (α t)) (Icc 0 T) t :=
    (solves hT k t ht).1.prodMk (solves hT k t ht).2
  have hα := ODE.contDiffOn_enat_Icc_of_hasDerivWithinAt hf hd (mapsTo_univ α _)
  exact contDiff_fst.comp_contDiffOn hα

/-- A smooth strict Jacobi weight for a compact family of directions in a
larger simple conformal chart. Curvature at the observation points and the
entrance data are continuous. Ray paths are smooth in arclength; no transverse
smooth dependence of these paths or their Jacobi fields is assumed.

The smooth function on entrance coordinates and time pulls back to a smooth
angular function wherever the geometric entrance map and travel time are
smooth. Along an orbit the entrance is fixed and travel time increases by the
flow parameter. -/
theorem exists_smooth_chart_profiles {P G : Type*} [TopologicalSpace P] [CompactSpace P]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    {lam : ℂ → ℝ} (simple : SimpleMetric lam) {T : ℝ} (hT : 0 ≤ T)
    (entry : P → G) (τ : P → ℝ) (z : G → ℝ → ℂ) (θ : G → ℝ → ℝ)
    (he : Continuous entry) (hτ : Continuous τ) (ht : ∀ p, τ p ∈ Ioo 0 T)
    (hk : Continuous (fun p => curvature lam (z (entry p) (τ p))))
    (hz : ∀ p, ContDiffOn ℝ ∞ (z (entry p)) (Icc 0 T))
    (hg : ∀ p, unitGeodesicOn lam (z (entry p)) (θ (entry p)) (Icc 0 (τ p)))
    (hdisk : ∀ p, ∀ t ∈ Icc 0 (τ p), z (entry p) t ∈ closedBall 0 1) :
    ∃ F : G × ℝ → ℝ, ContDiffOn ℝ ∞ F (univ ×ˢ Ioo 0 T) ∧ ∀ p : P,
      0 < F (entry p, τ p) ∧ deriv (deriv (fun s => F (entry p, s))) (τ p) +
        curvature lam (z (entry p) (τ p)) * F (entry p, τ p) < 0 := by
  let K := fun p => curvature lam (z (entry p) (τ p))
  apply glue_frozen_profiles isOpen_Ioo entry τ K he hτ hk ht
  intro q
  let κ := fun s => curvature lam (z (entry q) s)
  have hκ : ContDiffOn ℝ ∞ κ (Icc 0 T) :=
    (curvature_contDiff simple.smooth).comp_contDiffOn (hz q)
  let k : C(Icc 0 T, ℝ) := ⟨(Icc 0 T).restrict κ, hκ.continuousOn.restrict⟩
  let w := field hT k
  let S := entry ⁻¹' {entry q}
  have hS : IsCompact S := (isClosed_singleton.preimage he).isCompact
  have hsmooth : ContDiffOn ℝ ∞ w (Ioo 0 T) := (field_smoothOn hT κ hκ).mono Ioo_subset_Icc_self
  have hwat (p : P) := hsmooth.contDiffAt (isOpen_Ioo.mem_nhds (ht p))
  have hct (v : ℝ → ℝ) (hv : ContinuousOn v (Ioo 0 T)) : ContinuousOn (fun p => v (τ p)) S :=
    hv.comp hτ.continuousOn (fun p _ => ht p)
  have hpos (p : P) (hp : p ∈ S) : 0 < w (τ p) := by
    have heq : entry p = entry q := hp
    have sub : Icc 0 (τ p) ⊆ Icc 0 T := Icc_subset_Icc_right (ht p).2.le
    have hj : jacobiOn lam (z (entry q)) w (speed hT k) (Icc 0 (τ p)) := fun s h =>
      ⟨((solves hT k s (sub h)).1).mono sub, ((solves hT k s (sub h)).2).mono sub⟩
    exact normalized_jacobi_positive simple (ht p).1 (heq ▸ hg p)
      (heq ▸ hdisk p) hj (initial_values hT k).1 (initial_values hT k).2
  have hode (p : P) (hp : p ∈ S) : deriv (deriv w) (τ p) + K p * w (τ p) = 0 := by
    have heq : entry p = entry q := hp
    rw [show deriv (deriv w) (τ p) = _ from (interior_equation hT k (ht p)).2.2]
    change -(κ (τ p)) * w (τ p) + curvature lam (z (entry p) (τ p)) * w (τ p) = 0
    rw [heq]
    dsimp only [κ]
    ring
  obtain ⟨a, _, d, _, ε, hε, hweight⟩ := exists_uniform_weight hS τ K (fun _ => w)
    hτ.continuousOn (hct _ hsmooth.continuousOn)
    (hct _ ((hsmooth.deriv_of_isOpen isOpen_Ioo (m := 0) (by decide)).continuousOn))
    (fun p _ => (hwat p).of_le (by decide)) hpos hode
  refine ⟨weight a d w, ?_, ?_⟩
  · unfold weight
    exact hsmooth.mul (contDiffOn_const.sub (contDiffOn_const.mul (contDiffOn_const.mul contDiffOn_id).exp))
  · intro p heq
    obtain ⟨hpos, hr⟩ := hweight p heq
    exact ⟨hpos, hr.trans_lt (mul_neg_of_neg_of_pos (neg_lt_zero.mpr hε) hpos)⟩

/-- Pull a jointly smooth profile back by the smooth entrance and travel-time
maps. The local flow laws turn its strict ordinary Jacobi inequality into
the positive Schur limit for the actual angular function on direction space. -/
theorem angular_pullback {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (entry : E → G) (τ : E → ℝ)
    {U : Set ℝ} (hU : IsOpen U) (F : G × ℝ → ℝ) (hF : ContDiffOn ℝ ∞ F (univ ×ˢ U))
    (p : E) (φ : ℝ → E) (K : ℝ)
    (he : ContDiffAt ℝ ∞ entry p) (hτ : ContDiffAt ℝ ∞ τ p) (ht : τ p ∈ U)
    (hflow : ∀ᶠ s in 𝓝 (0 : ℝ), entry (φ s) = entry p ∧ τ (φ s) = τ p + s)
    (hpos : 0 < F (entry p, τ p))
    (hODE : deriv (deriv (fun s => F (entry p, s))) (τ p) + K * F (entry p, τ p) < 0) :
    let h := fun q => -Real.log (F (entry q, τ q))
    ContDiffAt ℝ ∞ h p ∧ 0 < deriv (deriv (h ∘ φ)) 0 - K - (deriv (h ∘ φ) 0) ^ 2 := by
  have hFp := hF.contDiffAt ((isOpen_univ.prod hU).mem_nhds (show (entry p, τ p) ∈ _ from ⟨trivial, ht⟩))
  refine ⟨((hFp.comp p (he.prodMk hτ)).log hpos.ne').neg, ?_⟩
  let g := fun t => -Real.log (F (entry p, t))
  have hg : (fun q => -Real.log (F (entry q, τ q))) ∘ φ =ᶠ[𝓝 0] (fun s => g (τ p + s)) := by
    filter_upwards [hflow] with s hs
    simp [g, hs]
  rw [hg.deriv_eq, hg.deriv.deriv_eq]
  have hshift : deriv (fun s => g (τ p + s)) = fun s => deriv g (τ p + s) :=
    funext (deriv_comp_const_add g (τ p))
  rw [hshift, deriv_comp_const_add]
  simp only [add_zero]
  have hfc : ContDiffAt ℝ 2 (fun s => F (entry p, s)) (τ p) :=
    (hFp.comp (τ p) (contDiffAt_const.prodMk contDiffAt_id)).of_le (by decide)
  rw [show deriv (deriv g) (τ p) - K - (deriv g (τ p)) ^ 2 = _ from negLog_schur_identity hfc hpos K]
  exact div_pos (neg_pos.mpr hODE) hpos

/-- The first and second time derivatives on a genuine integral curve equal
the first and iterated directional derivatives of the vector field. -/
theorem integral_curve_derivatives {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : E → E) (h : E → ℝ) (φ : ℝ → E) (p : E) (h0 : φ 0 = p)
    (dX : DifferentiableAt ℝ X p) (dh : ContDiffAt ℝ 2 h p)
    (hφ : ∀ᶠ s in 𝓝 (0 : ℝ), HasDerivAt φ (X (φ s)) s) :
    deriv (h ∘ φ) 0 = fderiv ℝ h p (X p) ∧ deriv (deriv (h ∘ φ)) 0 =
      fderiv ℝ (fun q => fderiv ℝ h q (X q)) p (X p) := by
  have hφ₀ := hφ.self_of_nhds
  have hφc : Tendsto φ (𝓝 0) (𝓝 p) := h0 ▸ hφ₀.continuousAt.tendsto
  have he : deriv (h ∘ φ) =ᶠ[𝓝 0] fun s => fderiv ℝ h (φ s) (X (φ s)) := by
    filter_upwards [hφ, hφc.eventually (dh.eventually (by decide))] with s hs hd
    exact ((hd.differentiableAt (by decide)).hasFDerivAt.comp_hasDerivAt s hs).deriv
  have hd : DifferentiableAt ℝ (fun q => fderiv ℝ h q (X q)) p :=
    ((dh.fderiv_right (m := 1) (by decide)).differentiableAt (by decide)).clm_apply dX
  refine ⟨by simpa only [h0] using he.self_of_nhds, ?_⟩
  rw [he.deriv_eq]
  subst p
  exact (hd.hasFDerivAt.comp_hasDerivAt 0 hφ₀).deriv

/-- A smooth angular potential with strictly positive limiting Schur complement
in ordinary iterated derivatives of the actual geodesic vector field. The
geometry supplies a simple larger disk, its smooth entrance coordinates and
its geodesic flow, including arclength along each in-disk segment. The weight,
its angular regularity, and the strict inequality are constructed. -/
theorem exists_invariant_angular_weight {E G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    {S : Set E} (hS : IsCompact S) {lam : ℂ → ℝ} (simple : SimpleMetric lam)
    {T : ℝ} (hT : 0 ≤ T) (entry : E → G) (τ : E → ℝ) (X : E → E) (φ : E → ℝ → E)
    (z : G → ℝ → ℂ) (θ : G → ℝ → ℝ)
    (he : ∀ p ∈ S, ContDiffAt ℝ ∞ entry p) (hτ : ∀ p ∈ S, ContDiffAt ℝ ∞ τ p)
    (ht : ∀ p ∈ S, τ p ∈ Ioo 0 T)
    (hk : ContinuousOn (fun p => curvature lam (z (entry p) (τ p))) S)
    (hz : ∀ p ∈ S, ContDiffOn ℝ ∞ (z (entry p)) (Icc 0 T))
    (hg : ∀ p ∈ S, unitGeodesicOn lam (z (entry p)) (θ (entry p)) (Icc 0 (τ p)))
    (hdisk : ∀ p ∈ S, ∀ t ∈ Icc 0 (τ p), z (entry p) t ∈ closedBall 0 1)
    (dX : ∀ p ∈ S, DifferentiableAt ℝ X p) (hzero : ∀ p ∈ S, φ p 0 = p)
    (hflow : ∀ p ∈ S, ∀ᶠ s in 𝓝 (0 : ℝ), HasDerivAt (φ p) (X (φ p s)) s ∧
      entry (φ p s) = entry p ∧ τ (φ p s) = τ p + s) :
    ∃ h : E → ℝ, (∀ p q, entry p = entry q → τ p = τ q → h p = h q) ∧ ∀ p ∈ S, ContDiffAt ℝ ∞ h p ∧
      0 < fderiv ℝ (fun q => fderiv ℝ h q (X q)) p (X p) -
        curvature lam (z (entry p) (τ p)) - (fderiv ℝ h p (X p)) ^ 2 := by
  letI : CompactSpace S := isCompact_iff_compactSpace.mp hS
  have hce : ContinuousOn entry S := fun p hp => (he p hp).continuousAt.continuousWithinAt
  have hct : ContinuousOn τ S := fun p hp => (hτ p hp).continuousAt.continuousWithinAt
  obtain ⟨F, hF, hgood⟩ := exists_smooth_chart_profiles (P := S) simple hT
    (fun p => entry p) (fun p => τ p) z θ hce.restrict hct.restrict
    (fun p => ht p p.property) hk.restrict (fun p => hz p p.property)
    (fun p => hg p p.property) (fun p => hdisk p p.property)
  let h := fun q => -Real.log (F (entry q, τ q))
  refine ⟨h, fun p q he ht => by simp [h, he, ht], ?_⟩
  intro p hp
  obtain ⟨hpos, hode⟩ := hgood ⟨p, hp⟩
  obtain ⟨hreg, hlim⟩ := angular_pullback entry τ isOpen_Ioo F hF p (φ p) _
    (he p hp) (hτ p hp) (ht p hp) ((hflow p hp).mono fun _ a => a.2) hpos hode
  have hd := integral_curve_derivatives X h (φ p) p (hzero p hp) (dX p hp)
    (hreg.of_le (by decide)) ((hflow p hp).mono fun _ a => a.1)
  change 0 < deriv (deriv (h ∘ φ p)) 0 - _ - (deriv (h ∘ φ p) 0) ^ 2 at hlim
  rw [hd.1, hd.2] at hlim
  exact ⟨hreg, hlim⟩

theorem exists_smooth_angular_weight {E G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    {S : Set E} (hS : IsCompact S) {lam : ℂ → ℝ} (simple : SimpleMetric lam)
    {T : ℝ} (hT : 0 ≤ T) (entry : E → G) (τ : E → ℝ) (X : E → E) (φ : E → ℝ → E)
    (z : G → ℝ → ℂ) (θ : G → ℝ → ℝ)
    (he : ∀ p ∈ S, ContDiffAt ℝ ∞ entry p) (hτ : ∀ p ∈ S, ContDiffAt ℝ ∞ τ p)
    (ht : ∀ p ∈ S, τ p ∈ Ioo 0 T)
    (hk : ContinuousOn (fun p => curvature lam (z (entry p) (τ p))) S)
    (hz : ∀ p ∈ S, ContDiffOn ℝ ∞ (z (entry p)) (Icc 0 T))
    (hg : ∀ p ∈ S, unitGeodesicOn lam (z (entry p)) (θ (entry p)) (Icc 0 (τ p)))
    (hdisk : ∀ p ∈ S, ∀ t ∈ Icc 0 (τ p), z (entry p) t ∈ closedBall 0 1)
    (dX : ∀ p ∈ S, DifferentiableAt ℝ X p) (hzero : ∀ p ∈ S, φ p 0 = p)
    (hflow : ∀ p ∈ S, ∀ᶠ s in 𝓝 (0 : ℝ), HasDerivAt (φ p) (X (φ p s)) s ∧
      entry (φ p s) = entry p ∧ τ (φ p s) = τ p + s) :
    ∃ h : E → ℝ, ∀ p ∈ S, ContDiffAt ℝ ∞ h p ∧
      0 < fderiv ℝ (fun q => fderiv ℝ h q (X q)) p (X p) -
        curvature lam (z (entry p) (τ p)) - (fderiv ℝ h p (X p)) ^ 2 := by
  obtain ⟨h, _, good⟩ := exists_invariant_angular_weight hS simple hT entry τ X φ z θ
    he hτ ht hk hz hg hdisk dX hzero hflow
  exact ⟨h, good⟩

end TransportOkaGrauert.SmoothJacobiFamily
