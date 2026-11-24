import TransportOkaGrauert.DivisorHull
import TransportOkaGrauert.SteinDivisor
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Global Stein conditions from the corrected fibre polynomial

The domain carries a specified complex surface atlas. Holomorphic functions
are mathlib's complex manifold-differentiable functions. The coordinate
conclusion gives open neighborhoods on which a pair of global holomorphic
functions and its inverse are complex differentiable.

The application to a simple metric requires an atlas for the transport
complex structure, nontrapping incidence, the regular integrating factors
and extensions, and the centre derivative formulas. These are geometric
inputs to the conditional theorem below.
-/

noncomputable section
namespace TransportOkaGrauert.SteinCriterion

open Set ChartedSpace Manifold Topology
open scoped ComplexConjugate ContDiff

abbrev Plane := ℂ × ℂ
local notation "I₂" => 𝓘(ℂ, Plane)
local notation "I₁" => 𝓘(ℂ, ℂ)

/-- The functions used in the definition of the holomorphic hull. -/
def holomorphicFunctions (Y : Type*) [TopologicalSpace Y] [ChartedSpace Plane Y] :
    Set (Y → ℂ) := {f | MDifferentiable I₂ I₁ f}

/-- Classical compact-hull, point-separation and global local-coordinate
conditions for a complex surface. -/
structure SteinConditions (Y : Type*) [TopologicalSpace Y] [ChartedSpace Plane Y] : Prop where
  compactHull : ∀ K : Set Y, IsCompact K →
    IsCompact (DivisorHull.testHull (holomorphicFunctions Y) K)
  separate : ∀ x y : Y, x ≠ y → ∃ f ∈ holomorphicFunctions Y, f x ≠ f y
  coordinates : ∀ x : Y, ∃ f ∈ holomorphicFunctions Y, ∃ g ∈ holomorphicFunctions Y,
    IsLocalDiffeomorphAt I₂ I₂ 1 (fun y => (f y, g y)) x

/-- The differential of a map to the complex coordinate plane, in the
preferred complex chart at the source point. Its arguments are tangent
vectors in that chart, not physical base/velocity coordinate vectors. -/
def chartDerivative {Y : Type*} [TopologicalSpace Y] [ChartedSpace Plane Y]
    (f : Y → Plane) (x : Y) : Plane →L[ℂ] Plane :=
  fderiv ℂ (f ∘ (chartAt Plane x).symm) (chartAt Plane x x)

/-- An injective chart derivative gives local complex coordinates in complex
dimension two, including holomorphic regularity of the inverse on an open set. -/
theorem localCoordinates_of_injective {Y : Type*} [TopologicalSpace Y] [ChartedSpace Plane Y]
    [IsManifold I₂ 1 Y] {f : Y → Plane} (hf : ContMDiff I₂ I₂ 1 f)
    (x : Y) (hinj : Function.Injective (chartDerivative f x)) :
    IsLocalDiffeomorphAt I₂ I₂ 1 f x := by
  let c := chartAt Plane x
  let g := f ∘ c.symm
  let a := c x
  have hx : x ∈ c.source := mem_chart_source _ _
  have ha : a ∈ c.target := c.map_source hx
  have hci : ContMDiffOn I₂ I₂ 1 c.symm c.target := contMDiffOn_chart_symm
  have hg : ContDiffAt ℂ 1 g a :=
    ((hf (c.symm a)).comp a (hci.contMDiffAt (c.open_target.mem_nhds ha))).contDiffAt
  let d := chartDerivative f x
  let e := (LinearEquiv.ofInjectiveEndo d.toLinearMap hinj).toContinuousLinearEquiv
  have hder : HasFDerivAt g (e : Plane →L[ℂ] Plane) a :=
    (hg.differentiableAt one_ne_zero).hasFDerivAt
  let v := hg.toOpenPartialHomeomorph g hder one_ne_zero
  have hav : a ∈ v.source := hg.mem_toOpenPartialHomeomorph_source hder one_ne_zero
  have hgai : ContDiffAt ℂ 1 v.symm (g a) := hg.to_localInverse hder one_ne_zero
  obtain ⟨t, ht, hat, hit⟩ := hgai.contDiffOn' le_rfl (by simp)
  simp at hit
  let b := c.trans (v.symm.restrOpen t ht).symm
  have hxb : x ∈ b.source := ⟨hx, hav, hat⟩
  have agrees : EqOn f b b.source := by
    intro y hy
    change f y = f (c.symm (c y))
    rw [c.left_inv hy.1]
  let φ : PartialDiffeomorph I₂ I₂ Y Plane 1 := {
    toPartialEquiv := b.toPartialEquiv
    open_source := b.open_source
    open_target := b.open_target
    contMDiffOn_toFun := hf.contMDiffOn.congr agrees.symm
    contMDiffOn_invFun := by
      intro y hy
      have hyb : v.symm y ∈ c.target := hy.2
      have hyt : y ∈ t := hy.1.2
      exact ((hci.contMDiffAt (c.open_target.mem_nhds hyb)).comp y
        ((hit.contDiffAt (ht.mem_nhds hyt)).contMDiffAt)).contMDiffWithinAt }
  exact ⟨φ, hxb, agrees⟩

/-- The base and the closed velocity disk in a fixed global oriented frame. -/
abbrev ClosedBundle (B : Type*) := B × Metric.closedBall (0 : ℂ) 1

/-- Restrict the base to an arbitrary open set, and the velocity to the open disk. -/
def interiorOver {B : Type*} [TopologicalSpace B] (U : TopologicalSpace.Opens B) :
    Set (ClosedBundle B) := {z | z.1 ∈ U ∧ ‖(z.2 : ℂ)‖ < 1}

/-- Correct the geodesic pencil polynomial by its scalar integrating factor. -/
def divisor {B : Type*} (w : B → B → ℂ) (H : B → ClosedBundle B → ℂ)
    (p : B) (z : ClosedBundle B) : ℂ :=
  H p z * FlatScalar.firstIntegral (w p z.1) (z.2 : ℂ)

/-- Data on the compact bundle used before choosing an open base set. The
vector coefficient vanishes precisely at its centre, as for the gradient
of half the squared distance. -/
structure Pencil (B : Type*) [TopologicalSpace B] where
  w : B → B → ℂ
  H : B → ClosedBundle B → ℂ
  continuous_w : ∀ p, Continuous (w p)
  continuous_H : ∀ p, Continuous (H p)
  nonzero_H : ∀ p z, H p z ≠ 0
  zero_w : ∀ p x, w p x = 0 ↔ x = p

variable {B : Type*} [TopologicalSpace B] (P : Pencil B)

abbrev Pencil.F (p : B) : ClosedBundle B → ℂ := divisor P.w P.H p

theorem Pencil.continuous_F (p : B) : Continuous (P.F p) := by
  have hw := (P.continuous_w p).comp (continuous_fst (X := B) (Y := Metric.closedBall (0 : ℂ) 1))
  have hv : Continuous (fun z : ClosedBundle B => (z.2 : ℂ)) :=
    continuous_subtype_val.comp continuous_snd
  exact (P.continuous_H p).mul (hw.sub ((hv.pow 2).mul (Complex.continuous_conj.comp hw)))

theorem Pencil.F_zero_iff (p : B) (z : ClosedBundle B) (hz : ‖(z.2 : ℂ)‖ < 1) :
    P.F p z = 0 ↔ z.1 = p :=
  (SteinDivisor.corrected_interior_zero_iff _ _ _ (P.nonzero_H p z) hz).trans (P.zero_w p z.1)

variable (U : TopologicalSpace.Opens B)

/-- At a unit direction based in the open set, an omitted centre lies on
its unoriented radial geodesic. -/
def UnitEscape : Prop :=
  ∀ z : ClosedBundle B, z.1 ∈ U → ‖(z.2 : ℂ)‖ = 1 →
    ∃ p ∉ U, ∃ r : ℝ, P.w p z.1 = r * (z.2 : ℂ)

/-- Both kinds of escape select an omitted centre. For a base escape the
centre is the base point itself, including at the corner of the two faces. -/
theorem Pencil.omittedCentre (escape : UnitEscape P U) (z : ClosedBundle B)
    (hz : z ∉ interiorOver U) : ∃ p ∉ U, P.F p z = 0 := by
  by_cases hb : z.1 ∈ U
  · have hvle : ‖(z.2 : ℂ)‖ ≤ 1 := by
      exact mem_closedBall_zero_iff.mp z.2.property
    have hv : ‖(z.2 : ℂ)‖ = 1 := le_antisymm hvle (le_of_not_gt fun h => hz ⟨hb, h⟩)
    obtain ⟨p, hp, hr⟩ := escape z hb hv
    have unit : (z.2 : ℂ) * conj (z.2 : ℂ) = 1 := by simp [Complex.mul_conj', hv]
    have hq := (SteinDivisor.firstIntegral_unit_zero_iff_parallel _ _ unit).mpr hr
    exact ⟨p, hp, by simp [Pencil.F, divisor, hq]⟩
  · exact ⟨z.1, hb, by simp [Pencil.F, divisor, (P.zero_w _ _).mpr rfl, FlatScalar.firstIntegral]⟩

/-- The first derivatives supplied by the distance and fibre computations.
The real linear change of coordinates identifies physical horizontal and
vertical vectors with tangent vectors in the chosen complex chart. The
horizontal derivative of the second component can be arbitrary. -/
def CentreJets {Y : Type*} [TopologicalSpace Y] [ChartedSpace Plane Y]
    (f : Y → Plane) (x : Y) (h μ : ℂ) : Prop :=
  ∃ T : Plane ≃L[ℝ] Plane,
    (∀ a b : ℂ, (chartDerivative f x (T (a, b))).1 = h * FlatScalar.firstIntegral a μ) ∧
    ∀ b : ℂ, (chartDerivative f x (T (0, b))).2 = b

theorem CentreJets.injective {Y : Type*} [TopologicalSpace Y] [ChartedSpace Plane Y]
    {f : Y → Plane} {x : Y} {h μ : ℂ} (jets : CentreJets f x h μ)
    (hh : h ≠ 0) (hμ : ‖μ‖ < 1) : Function.Injective (chartDerivative f x) := by
  obtain ⟨T, h₁, h₂⟩ := jets
  apply (injective_iff_map_eq_zero (chartDerivative f x)).mpr
  intro v hv
  obtain ⟨⟨a, b⟩, rfl⟩ := T.surjective v
  have ha : a = 0 := (SteinDivisor.corrected_interior_zero_iff h a μ hh hμ).mp
    ((h₁ a b).symm.trans (congrArg Prod.fst hv))
  subst a
  have hb : b = 0 := (h₂ b).symm.trans (congrArg Prod.snd hv)
  subst b
  exact T.map_zero

/-- The three classical Stein conditions on the part over any open base
set. Geometric construction of the complex atlas and complex regularity
and centre jets of the two functions are hypotheses. Compactness of the
hull, separation, and local biholomorphicity are conclusions. -/
theorem steinConditions_of_pencil [CompactSpace B]
    [ChartedSpace Plane (interiorOver U)] [IsManifold I₂ 1 (interiorOver U)]
    (escape : UnitEscape P U)
    (G : B → interiorOver U → ℂ)
    (regularF : ∀ p, ContMDiff I₂ I₁ 1 (fun z : interiorOver U => P.F p z.val))
    (regularG : ∀ p, ContMDiff I₂ I₁ 1 (G p))
    (fibreG : ∀ (p : B) (z : interiorOver U), z.val.1 = p → G p z = (z.val.2 : ℂ))
    (jets : ∀ z : interiorOver U, let p := z.val.1
      CentreJets (fun y : interiorOver U => (P.F p y.val, G p y)) z (P.H p z.val) (z.val.2 : ℂ)) :
    SteinConditions (interiorOver U) := by
  have holoF (p : B) : (fun z : interiorOver U => P.F p z.val) ∈ holomorphicFunctions _ :=
    (regularF p).mdifferentiable one_ne_zero
  have holoG (p : B) : G p ∈ holomorphicFunctions _ := (regularG p).mdifferentiable one_ne_zero
  constructor
  · intro K hK
    apply DivisorHull.isCompact_testHull_of_boundary_divisors
      (fun _ hf => MDifferentiable.continuous hf) _ hK
    intro z hz
    obtain ⟨p, hp, hzero⟩ := P.omittedCentre U escape z hz
    have nonzero (y : interiorOver U) : P.F p y.val ≠ 0 :=
      fun eq => hp ((P.F_zero_iff p y.val y.property.2).mp eq ▸ y.property.1)
    refine ⟨P.F p, P.continuous_F p, hzero, nonzero, ?_⟩
    intro y
    exact (differentiableAt_inv (𝕜 := ℂ) (nonzero y)).mdifferentiableAt.comp y
      ((regularF p y).mdifferentiableAt one_ne_zero)
  · intro x y hxy
    by_cases hb : y.val.1 = x.val.1
    · refine ⟨G x.val.1, holoG _, ?_⟩
      rw [fibreG _ x rfl, fibreG _ y hb]
      exact fun hv => hxy (Subtype.ext (Prod.ext hb.symm (Subtype.ext hv)))
    · refine ⟨_, holoF x.val.1, ?_⟩
      change P.F x.val.1 x.val ≠ P.F x.val.1 y.val
      rw [(P.F_zero_iff _ _ x.property.2).mpr rfl]
      exact fun eq => hb ((P.F_zero_iff _ _ y.property.2).mp eq.symm)
  · intro x
    refine ⟨_, holoF x.val.1, _, holoG x.val.1, ?_⟩
    apply localCoordinates_of_injective ((regularF _).prodMk_space (regularG _))
    exact (jets x).injective (P.nonzero_H _ _) x.property.2

/-- In physical coordinates centred at `x`, the base variable is the framed
distance gradient and the fibre variable is the increment of velocity. The
map from physical coordinates to the transport chart has invertible real
differential. Only real differentiability of the scalar factor is required. -/
def PhysicalCoordinates [ChartedSpace Plane (interiorOver U)] (x : interiorOver U) : Prop :=
  ∃ (ψ : Plane → interiorOver U) (T : Plane ≃L[ℝ] Plane),
    ψ 0 = x ∧ ContinuousAt ψ 0 ∧
    HasFDerivAt (chartAt Plane x ∘ ψ) (T : Plane →L[ℝ] Plane) 0 ∧
    DifferentiableAt ℝ (fun v => P.H x.val.1 (ψ v).val) 0 ∧
    ∀ᶠ v in 𝓝 0, P.w x.val.1 (ψ v).val.1 = v.1 ∧
      ((ψ v).val.2 : ℂ) = (x.val.2 : ℂ) + v.2

/-- Derive the full horizontal row from the product rule at the zero of the
pencil. On vertical vectors use only the identity of the second function
on the selected fibre. -/
theorem centreJets_of_physicalCoordinates
    [ChartedSpace Plane (interiorOver U)] [IsManifold I₂ 1 (interiorOver U)]
    (x : interiorOver U) (G : interiorOver U → ℂ)
    (regular : ContMDiff I₂ I₂ 1 (fun z : interiorOver U => (P.F x.val.1 z.val, G z)))
    (fibre : ∀ z : interiorOver U, z.val.1 = x.val.1 → G z = (z.val.2 : ℂ))
    (phys : PhysicalCoordinates P U x) :
    CentreJets (fun z : interiorOver U => (P.F x.val.1 z.val, G z)) x
      (P.H x.val.1 x.val) (x.val.2 : ℂ) := by
  obtain ⟨ψ, T, hψ, hcont, hT, hH, physical⟩ := phys
  let f := fun z : interiorOver U => (P.F x.val.1 z.val, G z)
  let c := chartAt Plane x
  let D := chartDerivative f x
  let μ := (x.val.2 : ℂ)
  have hx : x ∈ c.source := mem_chart_source _ _
  have hci : ContMDiffOn I₂ I₂ 1 c.symm c.target := contMDiffOn_chart_symm
  have hg : ContDiffAt ℂ 1 (f ∘ c.symm) (c x) :=
    ((regular _).comp _ (hci.contMDiffAt (c.open_target.mem_nhds (c.map_source hx)))).contDiffAt
  have hD : HasFDerivAt (f ∘ c.symm) D (c x) := (hg.differentiableAt one_ne_zero).hasFDerivAt
  have hD' : HasFDerivAt (f ∘ c.symm) (D.restrictScalars ℝ) ((c ∘ ψ) 0) := by
    simpa only [Function.comp_apply, hψ] using hD.restrictScalars ℝ
  have near : ∀ᶠ v in 𝓝 0, ψ v ∈ c.source := hcont (c.open_source.mem_nhds (hψ ▸ hx))
  have derivPair : HasFDerivAt (f ∘ ψ) ((D.restrictScalars ℝ).comp (T : Plane →L[ℝ] Plane)) 0 := by
    apply (hD'.comp 0 hT).congr_of_eventuallyEq
    filter_upwards [near] with v hv using (congrArg f (c.left_inv hv)).symm
  have ha := hasFDerivAt_fst (𝕜 := ℝ) (p := (0 : Plane))
  have hb := (hasFDerivAt_snd (𝕜 := ℝ) (p := (0 : Plane))).const_add μ
  have hc := Complex.conjCLE.hasFDerivAt.comp (0 : Plane) ha
  have prodRule := hH.hasFDerivAt.mul (ha.sub ((hb.pow 2).mul hc))
  have actualF := prodRule.congr_of_eventuallyEq (f₁ := fun v => P.F x.val.1 (ψ v).val) (by
    filter_upwards [physical] with v hv
    simp [Pencil.F, divisor, FlatScalar.firstIntegral, hv.1, hv.2, Complex.conjCLE_apply, μ])
  refine ⟨T, ?_, ?_⟩
  · intro a b
    have eq := DFunLike.congr_fun (derivPair.fst.unique actualF) (a, b)
    simpa [f, D, μ, FlatScalar.firstIntegral, hψ, ContinuousLinearMap.smulRight_apply,
      Complex.conjCLE_apply] using eq
  · let j := ContinuousLinearMap.inr ℝ ℂ ℂ
    have hpair : HasFDerivAt (f ∘ ψ) ((D.restrictScalars ℝ).comp (T : Plane →L[ℝ] Plane)) (j 0) := by
      simpa only [map_zero] using derivPair
    have hj : Filter.Tendsto j (𝓝 0) (𝓝 0) := by
      simpa only [map_zero] using j.continuous.continuousAt (x := 0)
    have ev := hj.eventually physical
    have hv : (fun v : ℂ => G (ψ (j v))) =ᶠ[𝓝 0] (fun v => μ + v) := by
      filter_upwards [ev] with v hv
      have hw : P.w x.val.1 (ψ (j v)).val.1 = 0 := hv.1
      rw [fibre _ ((P.zero_w _ _).mp hw)]
      exact hv.2
    have idDer := ((hasFDerivAt_id (𝕜 := ℝ) (0 : ℂ)).const_add μ).congr_of_eventuallyEq hv
    have eq := (hpair.snd.comp (0 : ℂ) j.hasFDerivAt).unique idDer
    intro b
    exact DFunLike.congr_fun eq b

/-- Subtract a multiple of the corrected divisor from the velocity expressed
in the radial frame. The frame change at the centre is normalized to one. -/
def fibreFunction (rotation : B → B → ℂ) (correction : B → interiorOver U → ℂ)
    (p : B) (z : interiorOver U) : ℂ :=
  rotation p z.val.1 * (z.val.2 : ℂ) - correction p z * P.F p z.val

/-- Assembly in terms of the two explicit function formulas. The analytic
input is the complex regularity of their corrected extensions. Physical
coordinate regularity and unit escape express separate geometric inputs.
Neither hull bounds, point separation, nor invertibility of the complex
coordinate pair are assumed. -/
theorem steinConditions_of_physicalCoordinates [CompactSpace B]
    [ChartedSpace Plane (interiorOver U)] [IsManifold I₂ 1 (interiorOver U)]
    (escape : UnitEscape P U)
    (rotation : B → B → ℂ) (rotation_at_centre : ∀ p, rotation p p = 1)
    (correction : B → interiorOver U → ℂ)
    (regularF : ∀ p, ContMDiff I₂ I₁ 1 (fun z : interiorOver U => P.F p z.val))
    (regularG : ∀ p, ContMDiff I₂ I₁ 1 (fibreFunction P U rotation correction p))
    (phys : ∀ x : interiorOver U, PhysicalCoordinates P U x) :
    SteinConditions (interiorOver U) := by
  let G := fibreFunction P U rotation correction
  have fibre (p : B) (z : interiorOver U) (h : z.val.1 = p) : G p z = (z.val.2 : ℂ) := by
    have hzero := (P.F_zero_iff p z.val z.property.2).mpr h
    simp [G, fibreFunction, hzero, h, rotation_at_centre]
  apply steinConditions_of_pencil P U escape G regularF regularG fibre
  intro x
  exact centreJets_of_physicalCoordinates P U x (G x.val.1)
    ((regularF _).prodMk_space (regularG _)) (fibre _) (phys x)

end TransportOkaGrauert.SteinCriterion
