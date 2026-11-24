import TransportOkaGrauert.CRCoordinates
import Mathlib.Geometry.Manifold.IsManifold.Basic

/-!
# A holomorphic atlas on the whole open transport disk bundle

Starting with the three fixed-chart Stein properties, take ordinary local
inverses of their CR coordinate pairs. The resulting open coordinate charts
cover the physical domain, and their transition maps and inverses are
holomorphic in the usual complex Fréchet derivative sense.
-/

noncomputable section

namespace TransportOkaGrauert.ChartSteinAtlas

open ChartStein CRCoordinates Set Metric
open scoped Topology ContDiff Manifold

/-- The open physical domain inside the ambient real chart. -/
def domain (U : Set ℂ) : Set E := U ×ˢ ball (0 : ℂ) 1

private def interiorPoint {U : Set ℂ} (hs : U ⊆ ball 0 1) (p : domain U) : interiorOver U :=
  ⟨(⟨p.val.1, ball_subset_closedBall (hs p.property.1)⟩,
    ⟨p.val.2, ball_subset_closedBall p.property.2⟩), p.property.1,
    mem_ball_zero_iff.mp p.property.2⟩

/-- The physical open domain and the interior used by the hull and separation
axioms have exactly the same topology. -/
def interiorHomeomorph {U : Set ℂ} (hs : U ⊆ ball 0 1) : domain U ≃ₜ interiorOver U where
  toFun := interiorPoint hs
  invFun p := ⟨point p.val, p.property.1, mem_ball_zero_iff.mpr p.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by unfold interiorPoint; fun_prop
  continuous_invFun := (continuous_point.comp continuous_subtype_val).subtype_mk _

/-- A chart is chosen at every point. Its two component functions are defined
and CR-holomorphic throughout the physical domain, even though its local
inverse is used only on the target of the chart. -/
structure HolomorphicCover (σ : ℂ → ℝ) (U : Set ℂ) where
  chart : domain U → OpenPartialHomeomorph E E
  centered : ∀ p, p.val ∈ (chart p).source
  source_subset : ∀ p, (chart p).source ⊆ domain U
  regular : ∀ p x, x ∈ (chart p).source → Function.Bijective (fderiv ℝ (chart p) x)
  components : ∀ p x, x ∈ domain U →
    HolAt σ (fun z => (chart p z).1) x ∧ HolAt σ (fun z => (chart p z).2) x
  holomorphic : ∀ p h, (∀ x ∈ (chart p).source, HolAt σ h x) →
    DifferentiableOn ℂ (h ∘ (chart p).symm) (chart p).target

theorem cover_of_stein {σ : ℂ → ℝ} {U : Set ℂ} (hU : IsOpen U) (hs : U ⊆ ball 0 1)
    (h : HasSteinProperties σ U) : Nonempty (HolomorphicCover σ U) := by
  classical
  choose f g hf hg hpair using fun p : domain U => h.coordinates (interiorPoint hs p)
  have hfc (p : domain U) (x : E) (hx : x ∈ domain U) : HolAt σ (f p) x :=
    hf p (interiorPoint hs ⟨x,hx⟩)
  have hgc (p : domain U) (x : E) (hx : x ∈ domain U) : HolAt σ (g p) x :=
    hg p (interiorPoint hs ⟨x,hx⟩)
  let F (p : domain U) (x : E) := (f p x, g p x)
  let O (p : domain U) := domain U ∩ interior {x | IsUnit (fderiv ℝ (F p) x)}
  have hpO (p : domain U) : p.val ∈ O p := by
    have df : ContDiffAt ℝ ∞ (F p) p.val := (hfc p p p.property).1.prodMk (hgc p p p.property).1
    exact ⟨p.property, mem_interior_iff_mem_nhds.mpr ((df.continuousAt_fderiv (by simp)).eventually
      (Units.isOpen.mem_nhds (ContinuousLinearMap.isUnit_iff_bijective.mpr (hpair p))))⟩
  choose e he hp hin hhol using fun p : domain U =>
    holomorphic_chart ((hU.prod isOpen_ball).inter isOpen_interior) (hpO p)
      (fun x hx => mem_ball_zero_iff.mp hx.1.2) (fun x hx => hfc p x hx.1)
      (fun x hx => hgc p x hx.1) (hpair p)
  refine ⟨⟨e,hp,fun p x hx => (hin p hx).1,?_,?_,hhol⟩⟩
  · intro p x hx
    rw [he p]
    have hum : x ∈ {y : E | IsUnit (fderiv ℝ (F p) y)} := interior_subset (hin p hx).2
    exact ContinuousLinearMap.isUnit_iff_bijective.mp hum
  intro p x hx
  simp only [he p]
  exact ⟨hfc p x hx,hgc p x hx⟩

namespace HolomorphicCover

variable {σ : ℂ → ℝ} {U : Set ℂ} (A : HolomorphicCover σ U)

theorem covers : (⋃ p, (A.chart p).source) = domain U := by
  apply Subset.antisymm (iUnion_subset A.source_subset)
  intro x hx
  exact mem_iUnion.mpr ⟨⟨x,hx⟩, A.centered ⟨x,hx⟩⟩

/-- The chart transition is complex differentiable on the exact overlap. -/
theorem transition (p q : domain U) :
    DifferentiableOn ℂ ((A.chart p).symm.trans (A.chart q))
      ((A.chart p).symm.trans (A.chart q)).source := by
  have hd (f : E → ℂ) (hf : ∀ x ∈ domain U, HolAt σ f x) :=
    A.holomorphic p f (fun x hx => hf x (A.source_subset p hx))
  have h1 := hd (fun x => (A.chart q x).1) (fun x hx => (A.components q x hx).1)
  have h2 := hd (fun x => (A.chart q x).2) (fun x hx => (A.components q x hx).2)
  exact (h1.prodMk h2).mono (fun _ h => h.1)

/-- Both functions in this open partial homeomorphism are ordinary
holomorphic maps on their respective domains. -/
theorem biholomorphic_transition (p q : domain U) :
    let e := (A.chart p).symm.trans (A.chart q)
    DifferentiableOn ℂ e e.source ∧ DifferentiableOn ℂ e.symm e.target :=
  ⟨A.transition p q, A.transition q p⟩

/-- The transitions are also C¹ over the complex numbers. Their real
derivatives are continuous by the real inverse function theorem and their
complex derivatives have exactly those restrictions of scalars. -/
theorem transition_C1 (p q : domain U) :
    ContDiffOn ℂ 1 ((A.chart p).symm.trans (A.chart q))
      ((A.chart p).symm.trans (A.chart q)).source := by
  let e := A.chart p
  let g := A.chart q
  let k := e.symm.trans g
  have hs : ContDiffOn ℝ ∞ k k.source := by
    intro y hy
    have hx : e.symm y ∈ domain U := A.source_subset p (e.map_target hy.1)
    have components (i : domain U) : ContDiffAt ℝ ∞ (A.chart i) (e.symm y) :=
      (A.components i _ hx).1.1.prodMk (A.components i _ hx).2.1
    have hb := A.regular p _ (e.map_target hy.1)
    let T := ContinuousLinearEquiv.ofBijective (fderiv ℝ e (e.symm y))
      (LinearMap.ker_eq_bot.mpr hb.1) (LinearMap.range_eq_top.mpr hb.2)
    have de : HasFDerivAt e T.toContinuousLinearMap (e.symm y) :=
      ((components p).differentiableAt (by simp)).hasFDerivAt
    exact ((components q).comp y (e.contDiffAt_symm hy.1 de (components p))).contDiffWithinAt
  have hd := A.transition p q
  apply (contDiffOn_succ_iff_fderiv_of_isOpen (n := 0) k.open_source).mpr
  refine ⟨hd,by simp,contDiffOn_zero.mpr ?_⟩
  have emb := (ContinuousLinearMap.restrictScalarsIsometry ℂ E E ℝ ℝ).isometry.isEmbedding
  apply emb.continuousOn_iff.mpr
  apply ((hs.fderiv_of_isOpen k.open_source (m := 0) (by decide)).continuousOn).congr
  intro y hy
  exact ((hd y hy).differentiableAt (k.open_source.mem_nhds hy)).fderiv_restrictScalars ℝ |>.symm

private def openDomain (hU : IsOpen U) : TopologicalSpace.Opens E :=
  ⟨domain U, hU.prod isOpen_ball⟩

/-- Restricting each ambient chart to the physical open subtype gives an
actual mathlib charted space on the original topology of the domain. -/
def localChart (hU : IsOpen U) (p : domain U) : OpenPartialHomeomorph (domain U) E :=
  (A.chart p).subtypeRestr (s := openDomain hU) ⟨p⟩

def chartedSpace (hU : IsOpen U) : ChartedSpace E (domain U) where
  atlas := range (A.localChart hU)
  chartAt := A.localChart hU
  mem_chart_source p := by
    change p ∈ ((A.chart p).subtypeRestr (s := openDomain hU) ⟨p⟩).source
    rw [OpenPartialHomeomorph.subtypeRestr_source]
    exact A.centered p
  chart_mem_atlas p := mem_range_self p

theorem isManifold_one (hU : IsOpen U) :
    letI := A.chartedSpace hU
    IsManifold 𝓘(ℂ,E) 1 (domain U) := by
  letI := A.chartedSpace hU
  apply isManifold_of_contDiffOn
  rintro _ _ ⟨p,rfl⟩ ⟨q,rfl⟩
  let e := (A.localChart hU p).symm.trans (A.localChart hU q)
  let k := (A.chart p).symm.trans (A.chart q)
  have lift (y : E) (hy : y ∈ e.source) : y ∈ k.source ∧ e y = k y := by
    have ht : y ∈ (A.localChart hU p).target := hy.1
    have eq := (A.chart p).subtypeRestr_symm_apply (U := openDomain hU) ⟨p⟩ ht
    change ((A.localChart hU p).symm y).val = (A.chart p).symm y at eq
    have hq : (A.localChart hU p).symm y ∈ (A.localChart hU q).source := hy.2
    change (A.localChart hU p).symm y ∈ ((A.chart q).subtypeRestr (s := openDomain hU) ⟨q⟩).source at hq
    rw [OpenPartialHomeomorph.subtypeRestr_source] at hq
    refine ⟨⟨(A.chart p).subtypeRestr_target_subset (s := openDomain hU) ⟨p⟩ ht, ?_⟩, ?_⟩
    · change (A.chart p).symm y ∈ (A.chart q).source
      rwa [← eq]
    · exact congrArg (A.chart q) eq
  have hc : ContDiffOn ℂ 1 e e.source :=
    ((A.transition_C1 p q).mono (fun _ h => (lift _ h).1)).congr (fun _ h => (lift _ h).2)
  change ContDiffOn ℂ 1 e (e.source ∩ range (id : E → E))
  simpa only [range_id, inter_univ] using hc

end HolomorphicCover

/-- The fixed-chart Stein properties give a covering of the full open domain,
biholomorphic transitions on every overlap and the complex manifold structure
on the original topology. -/
theorem atlas_of_stein {σ : ℂ → ℝ} {U : Set ℂ} (hU : IsOpen U) (hs : U ⊆ ball 0 1)
    (h : HasSteinProperties σ U) :
    ∃ A : HolomorphicCover σ U, (⋃ p, (A.chart p).source) = domain U ∧
      (∀ p q : domain U, let e := (A.chart p).symm.trans (A.chart q)
        DifferentiableOn ℂ e e.source ∧ DifferentiableOn ℂ e.symm e.target) ∧
      (letI := A.chartedSpace hU; IsManifold 𝓘(ℂ,E) 1 (domain U)) := by
  obtain ⟨A⟩ := cover_of_stein hU hs h
  exact ⟨A,A.covers,A.biholomorphic_transition,A.isManifold_one hU⟩

end TransportOkaGrauert.ChartSteinAtlas
