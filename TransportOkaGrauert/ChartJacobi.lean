import TransportOkaGrauert.StrictJacobiWeight
import TransportOkaGrauert.SimpleDiskTarget
import TransportOkaGrauert.WeightTransport

/-!
# Normalized Jacobi fields on simple conformal disks

The scalar field is obtained from a two-dimensional linear evolution.
The curvature can vary along the whole ray and with its entrance data.
The no-conjugate-points condition used below is the one in `SimpleMetric`.
-/

noncomputable section

namespace TransportOkaGrauert.ChartJacobi

open Filter Set Metric SimpleDiskTarget StrictJacobiWeight
open scoped Topology ContDiff

/-- No conjugate points excludes a second zero of the normalized normal Jacobi
field, including at the far endpoint of the closed geodesic segment. All
derivatives at the entrance and at the far endpoint are one-sided. -/
theorem normalized_jacobi_no_later_zeros {lam : ℂ → ℝ} (simple : SimpleMetric lam)
    {T : ℝ} (hT : 0 < T) {z : ℝ → ℂ} {θ j dj : ℝ → ℝ}
    (geo : unitGeodesicOn lam z θ (Icc 0 T))
    (hdisk : ∀ t ∈ Icc 0 T, z t ∈ closedBall 0 1)
    (hj : jacobiOn lam z j dj (Icc 0 T)) (h0 : j 0 = 0) (h1 : dj 0 = 1) :
    ∀ t ∈ Ioc 0 T, j t ≠ 0 := by
  have hinit := (hj 0 (left_mem_Icc.mpr hT.le)).1
  rw [h1] at hinit
  intro t ht hz
  have sub : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc_right ht.2
  have hg : unitGeodesicOn lam z θ (Icc 0 t) := fun u hu =>
    ⟨((geo u (sub hu)).1).mono sub, ((geo u (sub hu)).2).mono sub⟩
  have hj' : jacobiOn lam z j dj (Icc 0 t) := fun u hu =>
    ⟨((hj u (sub hu)).1).mono sub, ((hj u (sub hu)).2).mono sub⟩
  have heq := simple.noConjugate 0 t ht.1 z θ hg (fun u hu => hdisk u (sub hu)) j dj hj' h0 hz
  have hm := left_mem_Icc.mpr ht.1.le
  have hun := uniqueDiffOn_Icc ht.1 0 hm
  have hzero := (hasDerivWithinAt_const 0 (Icc 0 t) (0 : ℝ)).congr_of_mem heq hm
  linarith [(hinit.mono sub).derivWithin hun, hzero.derivWithin hun]

/-- The normalized normal Jacobi field is strictly positive after entry. -/
theorem normalized_jacobi_positive {lam : ℂ → ℝ} (simple : SimpleMetric lam)
    {T : ℝ} (hT : 0 < T) {z : ℝ → ℂ} {θ j dj : ℝ → ℝ}
    (geo : unitGeodesicOn lam z θ (Icc 0 T))
    (hdisk : ∀ t ∈ Icc 0 T, z t ∈ closedBall 0 1)
    (hj : jacobiOn lam z j dj (Icc 0 T)) (h0 : j 0 = 0) (h1 : dj 0 = 1) :
    0 < j T := by
  apply positive_of_no_later_zeros hT h0 _ (fun u hu => (hj u hu).1.continuousWithinAt)
    (normalized_jacobi_no_later_zeros simple hT geo hdisk hj h0 h1)
  simpa only [← h1] using (hj 0 (left_mem_Icc.mpr hT.le)).1

private abbrev E := ℝ × ℝ
private abbrev End₂ := E →L[ℝ] E

private def jacobiMatrix (k : ℝ) : End₂ :=
  (0 : E →L[ℝ] ℝ).prod (ContinuousLinearMap.fst ℝ ℝ ℝ) +
    k • (-(ContinuousLinearMap.snd ℝ ℝ ℝ)).prod 0

private theorem matrix_continuous : Continuous jacobiMatrix :=
  continuous_const.add (continuous_id.smul continuous_const)

private def readColumn (v : E) : End₂ →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.apply ℝ E v)

private def matrixPath {T : ℝ} (k : C(Icc 0 T, ℝ)) : C(Icc 0 T, End₂) :=
  ⟨fun s => jacobiMatrix (k s), matrix_continuous.comp k.continuous⟩

private theorem matrixPath_continuous {T : ℝ} : Continuous (@matrixPath T) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact matrix_continuous.comp continuous_eval

private def evolution {T : ℝ} (hT : 0 ≤ T) (k : C(Icc 0 T, ℝ)) (s : ℝ) : End₂ :=
  WeightTransport.along hT (WeightTransport.weight hT (matrixPath k)) s

private theorem evolution_continuous {T : ℝ} (hT : 0 ≤ T) :
    Continuous (fun q : C(Icc 0 T, ℝ) × ℝ => evolution hT q.1 q.2) := by
  exact continuous_eval.comp
    ((((WeightTransport.weight_continuous hT).comp matrixPath_continuous).comp continuous_fst).prodMk
      ((show Continuous (projIcc 0 T hT) from continuous_projIcc).comp continuous_snd))

/-- The normalized field for the prescribed curvature path, extended constantly
outside the time interval. -/
def field {T : ℝ} (hT : 0 ≤ T) (k : C(Icc 0 T, ℝ)) (s : ℝ) : ℝ :=
  readColumn (1, 0) (evolution hT k s)

/-- The normalized field's velocity, given by the second column of the same
evolution. It is the one-sided derivative also at the interval endpoints. -/
def speed {T : ℝ} (hT : 0 ≤ T) (k : C(Icc 0 T, ℝ)) (s : ℝ) : ℝ :=
  readColumn (0, 1) (evolution hT k s)

theorem field_continuous {T : ℝ} (hT : 0 ≤ T) :
    Continuous (fun q : C(Icc 0 T, ℝ) × ℝ => field hT q.1 q.2) :=
  (readColumn (1, 0)).continuous.comp (evolution_continuous hT)

theorem speed_continuous {T : ℝ} (hT : 0 ≤ T) :
    Continuous (fun q : C(Icc 0 T, ℝ) × ℝ => speed hT q.1 q.2) :=
  (readColumn (0, 1)).continuous.comp (evolution_continuous hT)

theorem initial_values {T : ℝ} (hT : 0 ≤ T) (k : C(Icc 0 T, ℝ)) :
    field hT k 0 = 0 ∧ speed hT k 0 = 1 := by
  have he : evolution hT k 0 = 1 := (WeightTransport.weight_solves hT (matrixPath k)).initial
  rw [field, speed, he]
  exact ⟨rfl, rfl⟩

theorem solves {T : ℝ} (hT : 0 ≤ T) (k : C(Icc 0 T, ℝ)) (t : ℝ) (ht : t ∈ Icc 0 T) :
    HasDerivWithinAt (field hT k) (speed hT k t) (Icc 0 T) t ∧
    HasDerivWithinAt (speed hT k) (-(k ⟨t, ht⟩) * field hT k t) (Icc 0 T) t := by
  have he : HasDerivWithinAt (evolution hT k) (evolution hT k t * jacobiMatrix (k ⟨t, ht⟩))
      (Icc 0 T) t := by
    have hd := (WeightTransport.weight_solves hT (matrixPath k)).deriv t ht
    simpa only [WeightTransport.along, projIcc_of_mem hT ht, matrixPath, evolution] using hd
  have hfst := (readColumn (1, 0)).hasFDerivAt.comp_hasDerivWithinAt t he
  have hsnd := (readColumn (0, 1)).hasFDerivAt.comp_hasDerivWithinAt t he
  have he₁ (v : ℝ) : jacobiMatrix v (1, 0) = (0, 1) := by simp [jacobiMatrix]
  have he₂ (v : ℝ) : jacobiMatrix v (0, 1) = (-v) • ((1, 0) : E) := by simp [jacobiMatrix]
  constructor
  · convert hfst using 1
    change (evolution hT k t (0, 1)).2 = (evolution hT k t (jacobiMatrix _ (1, 0))).2
    rw [he₁]
  · convert hsnd using 1
    change _ = (evolution hT k t (jacobiMatrix _ (0, 1))).2
    rw [he₂, map_smul]
    rfl

attribute [local irreducible] field speed evolution

private theorem regularity_of_system {U : Set ℝ} (hU : IsOpen U) {f v l : ℝ → ℝ}
    (hf : ∀ s ∈ U, HasDerivAt f (v s) s) (hv : ∀ s ∈ U, HasDerivAt v (l s) s)
    (hl : ContinuousOn l U) {t : ℝ} (ht : t ∈ U) :
    ContDiffAt ℝ 2 f t ∧ deriv f t = v t ∧ deriv (deriv f) t = l t := by
  have hvC : ContDiffOn ℝ 1 v U := by
    apply (contDiffOn_succ_iff_deriv_of_isOpen (n := 0) hU).mpr
    refine ⟨fun s hs => (hv s hs).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    exact (contDiffOn_zero.mpr hl).congr (fun s hs => (hv s hs).deriv)
  have hfC : ContDiffOn ℝ 2 f U := by
    apply (contDiffOn_succ_iff_deriv_of_isOpen (n := 1) hU).mpr
    refine ⟨fun s hs => (hf s hs).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    exact hvC.congr (fun s hs => (hf s hs).deriv)
  have he : deriv f =ᶠ[𝓝 t] v := by
    filter_upwards [hU.mem_nhds ht] with s hs
    exact (hf s hs).deriv
  exact ⟨hfC.contDiffAt (hU.mem_nhds ht), (hf t ht).deriv, he.deriv_eq.trans (hv t ht).deriv⟩

/-- At interior times there is no endpoint convention: the ordinary derivatives
of the field are the constructed velocity and minus curvature times the field. -/
theorem interior_equation {T : ℝ} (hT : 0 ≤ T) (k : C(Icc 0 T, ℝ)) {t : ℝ}
    (ht : t ∈ Ioo 0 T) :
    ContDiffAt ℝ 2 (field hT k) t ∧ deriv (field hT k) t = speed hT k t ∧
      deriv (deriv (field hT k)) t = -(k ⟨t, Ioo_subset_Icc_self ht⟩) * field hT k t := by
  let l (s : ℝ) := -(k (projIcc 0 T hT s)) * field hT k s
  have hkc : Continuous (fun s => k (projIcc 0 T hT s)) :=
    k.continuous.comp (show Continuous (projIcc 0 T hT) from continuous_projIcc)
  have hfc : Continuous (field hT k) := by
    simpa only [Function.comp_def] using (field_continuous hT).comp
      (show Continuous (fun s : ℝ => (k, s)) from continuous_const.prodMk continuous_id)
  have hl : Continuous l := hkc.neg.mul hfc
  have hf (s : ℝ) (hs : s ∈ Ioo 0 T) : HasDerivAt (field hT k) (speed hT k s) s :=
    ((solves hT k s (Ioo_subset_Icc_self hs)).1).hasDerivAt (Icc_mem_nhds hs.1 hs.2)
  have hv (s : ℝ) (hs : s ∈ Ioo 0 T) : HasDerivAt (speed hT k) (l s) s := by
    simpa only [l, projIcc_of_mem hT (Ioo_subset_Icc_self hs)] using
      ((solves hT k s (Ioo_subset_Icc_self hs)).2).hasDerivAt (Icc_mem_nhds hs.1 hs.2)
  simpa only [l, projIcc_of_mem hT (Ioo_subset_Icc_self ht)] using
    regularity_of_system isOpen_Ioo hf hv hl.continuousOn ht

/-- Curvature is smooth as a function of the base point of a smooth
ambient conformal chart. -/
theorem curvature_contDiff {lam : ℂ → ℝ} (h : ContDiff ℝ ∞ lam) :
    ContDiff ℝ ∞ (curvature lam) := by
  unfold curvature laplacian
  fun_prop

/-- Construction from chart geometry on a larger simple disk. The compact set
indexes the directions of interest, strictly after the entrance times and
strictly before the end of the coefficient interval. Only the segments up to
evaluation must stay in the larger disk. Joint continuity of the paths,
continuity of entrance and time, and their local flow law suffice for the
longitudinal conclusion. Continuity of the remaining angular jets is used only
when concluding uniform positivity of the full collar. -/
theorem exists_chart_flow_weight {P G : Type*} [TopologicalSpace P] [TopologicalSpace G]
    {S : Set P} (hS : IsCompact S) {lam : ℂ → ℝ} (simple : SimpleMetric lam)
    {T : ℝ} (hT : 0 ≤ T) (entry : P → G) (τ : P → ℝ) (φ : P → ℝ → P)
    (z : G → ℝ → ℂ) (θ : G → ℝ → ℝ)
    (he : ContinuousOn entry S) (hcτ : ContinuousOn τ S)
    (hz : Continuous (fun q : G × Icc 0 T => z q.1 q.2))
    (ht : ∀ p ∈ S, τ p ∈ Ioo 0 T)
    (hg : ∀ p ∈ S, unitGeodesicOn lam (z (entry p)) (θ (entry p)) (Icc 0 (τ p)))
    (hdisk : ∀ p ∈ S, ∀ t ∈ Icc 0 (τ p), z (entry p) t ∈ closedBall 0 1)
    (hflow : ∀ p ∈ S, ∀ᶠ s in 𝓝 (0 : ℝ),
      entry (φ p s) = entry p ∧ τ (φ p s) = τ p + s) :
    ∃ y : P → ℝ, ContinuousOn y S ∧ ∃ ε > 0,
      let h := fun p => -Real.log (y p)
      let K := fun p => curvature lam (z (entry p) (τ p))
      (∀ p ∈ S, 0 < y p ∧ ε ≤ deriv (deriv (h ∘ φ p)) 0 - K p - (deriv (h ∘ φ p) 0) ^ 2) ∧
      (∀ j : P → LeviBoundary.FrameJet, ContinuousJetOn j S →
        (∀ p ∈ S, (j p).curvature = K p ∧ (j p).x = deriv (h ∘ φ p) 0 ∧
          (j p).xx = deriv (deriv (h ∘ φ p)) 0) →
        ∃ η > 0, ∀ p ∈ S, ∀ t ∈ Ioo 0 η,
          0 < LeviBoundary.vertical t (j p) ∧ 0 < LeviBoundary.schur t (j p)) := by
  let K := fun p => curvature lam (z (entry p) (τ p))
  have hck : Continuous (fun q : G × Icc 0 T => curvature lam (z q.1 q.2)) :=
    (curvature_contDiff simple.smooth).continuous.comp hz
  let k (g : G) : C(Icc 0 T, ℝ) :=
    ⟨fun t => curvature lam (z g t), hck.comp
      (show Continuous (fun t : Icc 0 T => (g, t)) from continuous_const.prodMk continuous_id)⟩
  have hk : Continuous k := ContinuousMap.continuous_of_continuous_uncurry k hck
  let w := fun g => field hT (k g)
  have heval : ContinuousOn (fun p => (k (entry p), τ p)) S := (hk.comp_continuousOn he).prodMk hcτ
  have hc : ContinuousOn (fun p => w (entry p) (τ p)) S :=
    (field_continuous hT).comp_continuousOn heval
  have hc' : ContinuousOn (fun p => deriv (w (entry p)) (τ p)) S :=
    ((speed_continuous hT).comp_continuousOn heval).congr
      (fun p hp => (interior_equation hT (k (entry p)) (ht p hp)).2.1)
  have hinit (p : P) := initial_values hT (k (entry p))
  have henter p (hp : p ∈ S) : 0 < τ p ∧ w (entry p) 0 = 0 ∧
      HasDerivWithinAt (w (entry p)) 1 (Icc 0 (τ p)) 0 ∧
      ContinuousOn (w (entry p)) (Icc 0 (τ p)) ∧
      ∀ t ∈ Ioc 0 (τ p), w (entry p) t ≠ 0 := by
    have hτ := ht p hp
    let g := entry p
    have sub : Icc 0 (τ p) ⊆ Icc 0 T := Icc_subset_Icc_right hτ.2.le
    have hj : jacobiOn lam (z g) (w g) (speed hT (k g)) (Icc 0 (τ p)) := by
      intro s hs
      exact ⟨((solves hT (k g) s (sub hs)).1).mono sub,
        ((solves hT (k g) s (sub hs)).2).mono sub⟩
    have hd := (hj 0 (left_mem_Icc.mpr hτ.1.le)).1
    rw [(hinit p).2] at hd
    exact And.intro hτ.1 ⟨(hinit p).1, hd, fun s hs => (hj s hs).1.continuousWithinAt,
      normalized_jacobi_no_later_zeros simple hτ.1 (hg p hp) (hdisk p hp) hj
        (hinit p).1 (hinit p).2⟩
  have hode (p : P) (hp : p ∈ S) : deriv (deriv (w (entry p))) (τ p) +
      K p * w (entry p) (τ p) = 0 := by
    rw [show deriv (deriv (w (entry p))) (τ p) = _ from (interior_equation hT (k (entry p)) (ht p hp)).2.2]
    change -(K p) * _ + K p * _ = 0
    ring
  obtain ⟨a, _, d, _, ε, hε, hs⟩ :=
    exists_flow_weight_and_collar hS entry τ K w φ hcτ hc hc'
      (fun p hp => (interior_equation hT (k (entry p)) (ht p hp)).1) henter hode hflow
  refine ⟨fun p => weight a d (w (entry p)) (τ p), ?_, ε, hε, hs⟩
  exact hc.mul (continuousOn_const.sub (continuousOn_const.mul
    (Real.continuous_exp.comp_continuousOn (continuousOn_const.mul hcτ))))

end TransportOkaGrauert.ChartJacobi
