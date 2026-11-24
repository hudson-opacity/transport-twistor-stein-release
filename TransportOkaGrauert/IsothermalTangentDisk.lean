import TransportOkaGrauert.ChartSteinAtlas
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian

/-! # The intrinsic unit tangent disk in an isothermal chart

The genuine manifold derivative lifts an invertible smooth chart to the tangent
bundle. Multiplication by the conformal scale normalizes the chart velocity.
The metric identity then identifies the intrinsic open unit disk in every
fiber with the physical chart domain used by the Stein theorem.
-/

noncomputable section
namespace TransportOkaGrauert.IsothermalTangentDisk
open Set Filter Bundle Metric
open scoped Manifold Topology ContDiff
local notation "I₀" => 𝓘(ℝ,ℂ)

section charts
variable {M N : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold I₀ ∞ M]
    [TopologicalSpace N] [ChartedSpace ℂ N] [IsManifold I₀ ∞ N]

private theorem smooth_tangent {e : OpenPartialHomeomorph M N} (he : ContMDiffOn I₀ I₀ ∞ e e.source) :
    ContinuousOn (tangentMap I₀ I₀ e) {p : TangentBundle I₀ M | p.1 ∈ e.source} := by
  apply (he.continuousOn_tangentMapWithin (by simp) e.open_source.uniqueMDiffOn).congr
  intro p hp
  exact (tangentMapWithin_eq_tangentMap (e.open_source.uniqueMDiffWithinAt hp)
    (((he p.1 hp).contMDiffAt (e.open_source.mem_nhds hp)).mdifferentiableAt (by simp))).symm

private theorem tangent_left (e : OpenPartialHomeomorph M N) (he : ContMDiffOn I₀ I₀ ∞ e e.source)
    (hi : ContMDiffOn I₀ I₀ ∞ e.symm e.target) (p : TangentBundle I₀ M) (hp : p.1 ∈ e.source) :
    tangentMap I₀ I₀ e.symm (tangentMap I₀ I₀ e p) = p := by
  have de := ((he _ hp).contMDiffAt (e.open_source.mem_nhds hp)).mdifferentiableAt (by simp)
  have hy := e.map_source hp
  have di := ((hi _ hy).contMDiffAt (e.open_target.mem_nhds hy)).mdifferentiableAt (by simp)
  rw [← tangentMap_comp_at p di de]
  have unique := e.open_source.uniqueMDiffWithinAt (I := I₀) hp
  rw [← tangentMapWithin_eq_tangentMap unique (di.comp _ de),
    tangentMapWithin_congr (I := I₀) (I' := I₀) (f := e.symm ∘ e) (f₁ := id) (fun x hx => e.left_inv hx) p hp,
    tangentMapWithin_id unique]

/-- Tangent lift of a smooth chart with smooth inverse, with its actual
derivative as fiber map. -/
def tangentChart (e : OpenPartialHomeomorph M N) (he : ContMDiffOn I₀ I₀ ∞ e e.source)
    (hi : ContMDiffOn I₀ I₀ ∞ e.symm e.target) : OpenPartialHomeomorph (TangentBundle I₀ M) (TangentBundle I₀ N) where
  toFun := tangentMap I₀ I₀ e
  invFun := tangentMap I₀ I₀ e.symm
  source := {p | p.1 ∈ e.source}
  target := {q | q.1 ∈ e.target}
  map_source' := fun _ hp => e.map_source hp
  map_target' := fun _ hq => e.map_target hq
  left_inv' := tangent_left e he hi
  right_inv' := tangent_left e.symm hi he
  open_source := e.open_source.preimage (FiberBundle.continuous_proj _ _)
  open_target := e.open_target.preimage (FiberBundle.continuous_proj _ _)
  continuousOn_toFun := smooth_tangent he
  continuousOn_invFun := smooth_tangent (e := e.symm) hi

end charts

/-- The conformal change from ordinary coordinate velocities to the unit-frame
fiber coordinates of the transport twistor disk. -/
def normalize (σ : ℂ → ℝ) (hσ : Continuous σ) : (ℂ × ℂ) ≃ₜ (ℂ × ℂ) where
  toFun p := (p.1,Real.exp (σ p.1) • p.2)
  invFun p := (p.1,Real.exp (-σ p.1) • p.2)
  left_inv p := by
    change (p.1,Real.exp (-σ p.1) • Real.exp (σ p.1) • p.2) = p
    simp only [smul_smul,← Real.exp_add,neg_add_cancel,Real.exp_zero,one_smul]
  right_inv p := by
    change (p.1,Real.exp (σ p.1) • Real.exp (-σ p.1) • p.2) = p
    simp only [smul_smul,← Real.exp_add,add_neg_cancel,Real.exp_zero,one_smul]
  continuous_toFun := continuous_fst.prodMk ((Real.continuous_exp.comp (hσ.comp continuous_fst)).smul continuous_snd)
  continuous_invFun := continuous_fst.prodMk ((Real.continuous_exp.comp (hσ.comp continuous_fst).neg).smul continuous_snd)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold I₀ ∞ M]

/-- The physical coordinates of an actual tangent vector. -/
def physicalChart (e : OpenPartialHomeomorph M ℂ) (he : ContMDiffOn I₀ I₀ ∞ e e.source)
    (hi : ContMDiffOn I₀ I₀ ∞ e.symm e.target) (σ : ℂ → ℝ) (hσ : Continuous σ) :
    OpenPartialHomeomorph (TangentBundle I₀ M) (ℂ × ℂ) :=
  (tangentChart e he hi).transHomeomorph ((tangentBundleModelSpaceHomeomorph I₀).trans (normalize σ hσ))

theorem physicalChart_apply (e : OpenPartialHomeomorph M ℂ) (he : ContMDiffOn I₀ I₀ ∞ e e.source)
    (hi : ContMDiffOn I₀ I₀ ∞ e.symm e.target) (σ : ℂ → ℝ) (hσ : Continuous σ) (p : TangentBundle I₀ M) :
    physicalChart e he hi σ hσ p = (e p.1,Real.exp (σ (e p.1)) • (mfderiv I₀ I₀ e p.1 p.2 : ℂ)) := rfl

/-- The isothermal metric identity on a chart, stated on actual manifold
tangent vectors using the Riemannian fiber metric. -/
def IsothermalFor (g : Bundle.RiemannianMetric (TangentSpace I₀ : M → Type _))
    (e : OpenPartialHomeomorph M ℂ) (σ : ℂ → ℝ) :=
  ∀ (x : M), x ∈ e.source → ∀ v : TangentSpace I₀ x,
    g.inner x v v = Real.exp (2*σ (e x)) * (@norm ℂ _ (mfderiv I₀ I₀ e x v))^2

theorem metric_speed_sq {g : Bundle.RiemannianMetric (TangentSpace I₀ : M → Type _)}
    {e : OpenPartialHomeomorph M ℂ} {σ : ℂ → ℝ} (metric : IsothermalFor g e σ)
    (he : ContMDiffOn I₀ I₀ ∞ e e.source) (hi : ContMDiffOn I₀ I₀ ∞ e.symm e.target)
    (hσ : Continuous σ) (p : TangentBundle I₀ M) (hp : p.1 ∈ e.source) :
    ‖(physicalChart e he hi σ hσ p).2‖^2 = g.inner p.1 p.2 p.2 := by
  rw [metric p.1 hp,physicalChart_apply,norm_smul,Real.norm_of_nonneg (Real.exp_pos _).le,mul_pow,← Real.exp_nat_mul]
  norm_num

/-- The squared metric norm cuts out the intrinsic open unit tangent disks. -/
def intrinsicDisk (g : Bundle.RiemannianMetric (TangentSpace I₀ : M → Type _))
    (e : OpenPartialHomeomorph M ℂ) (U : Set ℂ) :=
  {p : TangentBundle I₀ M | p.1 ∈ e.source ∧ e p.1 ∈ U ∧ g.inner p.1 p.2 p.2 < 1}

/-- On every base set in the isothermal chart the metric unit tangent disk is
homeomorphic to the physical transport twistor domain, even without a globally
chosen frame on the abstract surface. -/
def diskHomeomorph {g : Bundle.RiemannianMetric (TangentSpace I₀ : M → Type _)}
    {e : OpenPartialHomeomorph M ℂ} {σ : ℂ → ℝ} (metric : IsothermalFor g e σ)
    (he : ContMDiffOn I₀ I₀ ∞ e e.source) (hi : ContMDiffOn I₀ I₀ ∞ e.symm e.target)
    (hσ : Continuous σ) (U : Set ℂ) (sub : U ⊆ e.target) :
    intrinsicDisk g e U ≃ₜ ChartSteinAtlas.domain U := by
  let c := physicalChart e he hi σ hσ
  have mem (p : TangentBundle I₀ M) (hp : p.1 ∈ e.source) :
      p ∈ intrinsicDisk g e U ↔ c p ∈ ChartSteinAtlas.domain U := by
    have eq := metric_speed_sq metric he hi hσ p hp
    change (p.1 ∈ e.source ∧ e p.1 ∈ U ∧ _) ↔ e p.1 ∈ U ∧ (c p).2 ∈ ball (0:ℂ) 1
    rw [mem_ball_zero_iff,← eq]
    have nonneg := norm_nonneg (c p).2
    have sq : ‖(c p).2‖^2 < 1 ↔ ‖(c p).2‖ < 1 := by constructor <;> intro h <;> nlinarith
    tauto
  have back (y : ChartSteinAtlas.domain U) : y.1 ∈ c.target := sub y.2.1
  have pre (y : ChartSteinAtlas.domain U) : c.symm y.1 ∈ intrinsicDisk g e U := by
    apply (mem _ (c.map_target (back y))).mpr
    rw [c.right_inv (back y)]
    exact y.2
  exact
    { toFun := fun p => ⟨c p.1,(mem _ p.2.1).mp p.2⟩
      invFun := fun y => ⟨c.symm y.1,pre y⟩
      left_inv := fun p => Subtype.ext (c.left_inv p.2.1)
      right_inv := fun y => Subtype.ext (c.right_inv (back y))
      continuous_toFun := (c.continuousOn.comp_continuous continuous_subtype_val (fun p => p.2.1)).subtype_mk _
      continuous_invFun := (c.symm.continuousOn.comp_continuous continuous_subtype_val back).subtype_mk _ }

end TransportOkaGrauert.IsothermalTangentDisk
