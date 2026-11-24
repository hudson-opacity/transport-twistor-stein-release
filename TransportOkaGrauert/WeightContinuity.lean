import Mathlib.Analysis.LocallyConvex.Barrelled
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Tactic

/-!
# Operator-norm continuity with respect to weights

A linear weight-to-operator map pulls back the operator norm to a seminorm.
Closed norm sublevels make that seminorm lower semicontinuous. On a Baire
topological vector space, barrelledness makes it continuous. The target norm
can have a stronger topology than the scalar pairings used to test it.
-/

namespace TransportOkaGrauert.WeightContinuity

open Set Filter Bornology
open scoped Topology

variable {W Y : Type*} [AddCommGroup W] [Module ℝ W] [TopologicalSpace W]
    [IsTopologicalAddGroup W] [ContinuousConstSMul ℝ W] [BaireSpace W]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Baire upgrade for every linear operator-valued weight parameter. No
completeness of the target or local norm on the source is required. -/
theorem continuous_of_closed_sublevels (T : W →ₗ[ℝ] Y)
    (closed : ∀ r : ℝ, IsClosed {w : W | ‖T w‖ ≤ r}) : Continuous T := by
  let p := (normSeminorm ℝ Y).comp T
  have lsc : LowerSemicontinuous p := lowerSemicontinuous_iff_isClosed_preimage.mpr closed
  have hp := p.continuous_of_lowerSemicontinuous lsc
  apply continuous_of_continuousAt_zero T
  rw [ContinuousAt, map_zero, tendsto_zero_iff_norm_tendsto_zero]
  change Tendsto p (𝓝 0) (𝓝 0)
  simpa only [map_zero] using hp.tendsto (0 : W)

/-- A norming collection of scalar tests suffices: its sublevel intersection
must recover the target norm sublevel. The tests need only be continuous
after restriction to the given family. -/
theorem continuous_of_norming_tests {ι : Type*} (T : W →ₗ[ℝ] Y) (test : ι → Y → ℝ)
    (norming : ∀ y r, ‖y‖ ≤ r ↔ ∀ i, test i y ≤ r)
    (hc : ∀ i, Continuous (fun w => test i (T w))) : Continuous T := by
  apply continuous_of_closed_sublevels
  intro r
  have he : {w : W | ‖T w‖ ≤ r} = ⋂ i, {w | test i (T w) ≤ r} := by
    ext w
    simpa only [mem_setOf_eq, mem_iInter] using norming (T w) r
  rw [he]
  exact isClosed_iInter fun i => isClosed_le (hc i) continuous_const

/-- For a fixed bounded operator, norm-dense vectors and dual vectors detect
the full operator norm bound. The test sets can consist of smooth fields. -/
theorem opNorm_le_iff_dense_pairings {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] Y) {s : Set E} {d : Set (Y →L[ℝ] ℝ)}
    (hs : Dense s) (hd : Dense d) {r : ℝ} (hr : 0 ≤ r) :
    ‖L‖ ≤ r ↔ ∀ x ∈ s, ∀ l ∈ d, l (L x) ≤ ‖l‖ * (r * ‖x‖) := by
  constructor
  · intro h x _ l _
    exact (le_abs_self _).trans ((l.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (L.le_of_opNorm_le h x) (norm_nonneg _)))
  · intro tests
    have allDual (x : E) (hx : x ∈ s) (l : Y →L[ℝ] ℝ) : l (L x) ≤ ‖l‖ * (r * ‖x‖) := by
      let e := ContinuousLinearMap.apply ℝ ℝ (L x)
      have hc : IsClosed {l : Y →L[ℝ] ℝ | l (L x) ≤ ‖l‖ * (r * ‖x‖)} :=
        isClosed_le e.continuous (continuous_norm.mul continuous_const)
      exact closure_minimal (fun l hl => tests x hx l hl) hc (hd l)
    have all (x : E) (l : Y →L[ℝ] ℝ) : l (L x) ≤ ‖l‖ * (r * ‖x‖) := by
      have hc : IsClosed {x : E | l (L x) ≤ ‖l‖ * (r * ‖x‖)} :=
        isClosed_le (l.continuous.comp L.continuous)
          (continuous_const.mul (continuous_const.mul continuous_norm))
      exact closure_minimal (fun x hx => allDual x hx l) hc (hs x)
    apply L.opNorm_le_bound hr
    intro x
    obtain ⟨l, hl, heq⟩ := exists_dual_vector'' ℝ (L x)
    change l (L x) = ‖L x‖ at heq
    rw [← heq]
    exact (all x l).trans (mul_le_of_le_one_left (mul_nonneg hr (norm_nonneg _)) hl)

/-- Scalar weak pairings with norm-dense smooth tests suffice for continuity
in the full operator norm. The operator family is linear in the weight. -/
theorem operatorNorm_continuous_of_dense_weak_tests {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : W →ₗ[ℝ] (E →L[ℝ] Y)) {s : Set E} {d : Set (Y →L[ℝ] ℝ)}
    (hs : Dense s) (hd : Dense d)
    (weak : ∀ x ∈ s, ∀ l ∈ d, Continuous (fun w => l (T w x))) : Continuous T := by
  apply continuous_of_closed_sublevels
  intro r
  by_cases hr : 0 ≤ r
  · have he : {w : W | ‖T w‖ ≤ r} = ⋂ (x : s) (l : d),
          {w | l.val (T w x.val) ≤ ‖l.val‖ * (r * ‖x.val‖)} := by
      ext w
      simp only [mem_setOf_eq, mem_iInter, Subtype.forall]
      exact opNorm_le_iff_dense_pairings (T w) hs hd hr
    rw [he]
    exact isClosed_iInter fun x => isClosed_iInter fun l =>
      isClosed_le (weak x x.property l l.property) continuous_const
  · convert isClosed_empty (X := W) using 1
    exact eq_empty_iff_forall_notMem.mpr fun w hw => hr ((norm_nonneg _).trans hw)

/-- The unrestricted weak operator topology suffices in particular. -/
theorem operatorNorm_continuous_of_weak_tests {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : W →ₗ[ℝ] (E →L[ℝ] Y))
    (weak : ∀ (x : E) (l : Y →L[ℝ] ℝ), Continuous (fun w => l (T w x))) :
    Continuous T := operatorNorm_continuous_of_dense_weak_tests T dense_univ dense_univ
      (fun x _ l _ => weak x l)

section Bilinear
variable {U V Z : Type*} [AddCommGroup U] [Module ℝ U] [UniformSpace U] [IsUniformAddGroup U]
    [ContinuousSMul ℝ U] [BaireSpace U] [FirstCountableTopology U]
    [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [FirstCountableTopology V]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- Separate continuity of a bilinear map on two Fréchet spaces gives joint
norm continuity. Baire is needed only in the variable on which uniform
boundedness is used. -/
theorem bilinear_jointly_continuous (B : U →ₗ[ℝ] V →ₗ[ℝ] Z)
    (left : ∀ v, Continuous (fun u => B u v)) (right : ∀ u, Continuous (B u)) :
    Continuous (fun p : U × V => B p.1 p.2) := by
  apply SeqContinuous.continuous
  intro q p hq
  have hu := continuous_fst.continuousAt.tendsto.comp hq
  have hv := continuous_snd.continuousAt.tendsto.comp hq
  let L (n : ℕ) : U →L[ℝ] Z := ⟨B.flip (q n).2, left _⟩
  have bound (u : U) : IsVonNBounded ℝ (range fun n => L n u) :=
    ((right u).continuousAt.tendsto.comp hv).isVonNBounded_range ℝ
  have equi := (PolynormableSpace.banach_steinhaus (𝓕 := L) bound).equicontinuous p.1
  have hd : Tendsto (fun n => L n (q n).1 - L n p.1) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [hu.eventually (Metric.equicontinuousAt_iff_right.mp equi ε hε)] with n hn
    rw [dist_zero_right, ← dist_eq_norm, dist_comm]
    exact hn n
  have hbase := (right p.1).continuousAt.tendsto.comp hv
  simpa only [Function.comp_def, L, ContinuousLinearMap.coe_mk', LinearMap.flip_apply,
    sub_add_cancel, zero_add] using hd.add hbase

/-- In a real bilinear polarized family of bounded operators, separate
continuity of dense scalar test pairings implies joint operator-norm
continuity. In particular, the diagonal normal operator is norm-continuous
along every continuous weight path. -/
theorem polarized_operatorNorm_continuous {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : U →ₗ[ℝ] U →ₗ[ℝ] (E →L[ℝ] Z)) {s : Set E} {d : Set (Z →L[ℝ] ℝ)}
    (hs : Dense s) (hd : Dense d)
    (left : ∀ v, ∀ x ∈ s, ∀ l ∈ d, Continuous (fun u => l (B u v x)))
    (right : ∀ u, ∀ x ∈ s, ∀ l ∈ d, Continuous (fun v => l (B u v x))) :
    Continuous (fun p : U × U => B p.1 p.2) ∧ Continuous (fun u => B u u) := by
  have joint := bilinear_jointly_continuous B
    (fun v => operatorNorm_continuous_of_dense_weak_tests (B.flip v) hs hd (left v))
    (fun u => operatorNorm_continuous_of_dense_weak_tests (B u) hs hd (right u))
  exact ⟨joint, joint.comp (continuous_id.prodMk continuous_id)⟩

end Bilinear

end TransportOkaGrauert.WeightContinuity
