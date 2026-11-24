import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-! # Smooth composition on the Banach space of continuous paths
This gives the nonlinearity in the path-space implicit equation for smooth
geodesic dependence. The parameter space can be any compact space. -/
namespace TransportOkaGrauert.SmoothPathComposition
noncomputable section
open Set Metric Filter Asymptotics
open scoped ContDiff Topology
variable {K E F : Type} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

private def applyAlong (L : C(K,E →L[ℝ] F)) (v : C(K,E)) : C(K,F) :=
  ⟨fun s => L s (v s),L.continuous.clm_apply v.continuous⟩

private def applyBilinear : C(K,E →L[ℝ] F) →ₗ[ℝ] C(K,E) →ₗ[ℝ] C(K,F) :=
  LinearMap.mk₂ ℝ (applyAlong (K := K) (E := E) (F := F))
    (fun _ _ _ => by ext s; rfl) (fun _ _ _ => by ext s; rfl)
    (fun L v w => ContinuousMap.ext (fun s => (L s).map_add (v s) (w s)))
    (fun c L v => ContinuousMap.ext (fun s => (L s).map_smul c (v s)))

private theorem eval_bound (L : C(K,E →L[ℝ] F)) (v : C(K,E)) :
    ‖(applyBilinear (K := K) (E := E) (F := F)) L v‖ ≤ 1 * ‖L‖ * ‖v‖ := by
  rw [one_mul]
  apply (ContinuousMap.norm_le (applyAlong L v) (mul_nonneg (norm_nonneg L) (norm_nonneg v))).mpr
  intro s
  exact ((L s).le_opNorm (v s)).trans (mul_le_mul (L.norm_coe_le_norm s)
    (v.norm_coe_le_norm s) (norm_nonneg _) (norm_nonneg _))

def evaluation : C(K,E →L[ℝ] F) →L[ℝ] C(K,E) →L[ℝ] C(K,F) :=
  LinearMap.mkContinuous₂ (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜₃ := ℝ) (σ₂₃ := RingHom.id ℝ)
    (σ₁₃ := RingHom.id ℝ) (E := C(K,E →L[ℝ] F)) (F := C(K,E)) (G := C(K,F)) (applyBilinear (K := K) (E := E) (F := F)) 1 eval_bound


theorem derivative (f : E → F) (hf : ContDiff ℝ ∞ f) (v : C(K,E)) :
    HasFDerivAt (ContinuousMap.comp (⟨f,hf.continuous⟩ : C(E,F)))
      (evaluation (K := K) (E := E) (F := F) (ContinuousMap.comp (⟨fderiv ℝ f, hf.continuous_fderiv (by simp)⟩ :
        C(E, E →L[ℝ] F)) v)) v := by
  let D : C(E,E →L[ℝ] F) := ⟨fderiv ℝ f,hf.continuous_fderiv (by simp)⟩
  have hD : Continuous (fun x : C(K,E) => D.comp x) := ContinuousMap.continuous_postcomp D
  rw [hasFDerivAt_iff_isLittleO_nhds_zero,isLittleO_iff]
  intro ε hε
  obtain ⟨δ,hδ,close⟩ := (Metric.continuousAt_iff (α := C(K,E)) (β := C(K,E →L[ℝ] F))).mp (hD.continuousAt (x := v)) ε hε
  filter_upwards [Metric.ball_mem_nhds (0 : C(K,E)) hδ] with h hh
  have dh : ‖h‖ < δ := by simpa using hh
  apply (ContinuousMap.norm_le _ (mul_nonneg hε.le (norm_nonneg h))).mpr
  intro s
  have osc (y : E) (hy : y ∈ ball (v s) δ) : ‖fderiv ℝ f y - fderiv ℝ f (v s)‖ ≤ ε := by
    let w := v + ContinuousMap.const K (y - v s)
    have hvw : dist w v < δ := by
      rw [dist_eq_norm_sub,show w-v = ContinuousMap.const K (y-v s) by simp [w]]
      exact ((ContinuousMap.norm_le _ (norm_nonneg (y-v s))).mpr (fun _ => le_rfl)).trans_lt
        (show ‖y-v s‖ < δ from dist_eq_norm_sub y (v s) ▸ hy)
    have hc := (ContinuousMap.dist_le (dist_nonneg : 0 ≤ dist (D.comp w) (D.comp v))).mp le_rfl s
    have hs : w s = y := by simp [w]
    simpa only [ContinuousMap.comp_apply,hs,dist_eq_norm_sub,D,ContinuousMap.coe_mk] using
      hc.trans (close hvw).le
  have hb : v s+h s ∈ ball (v s) δ := by
    rw [Metric.mem_ball,dist_eq_norm_sub,add_sub_cancel_left]
    exact (h.norm_coe_le_norm s).trans_lt dh
  have row := (convex_ball (v s) δ).norm_image_sub_le_of_norm_fderiv_le'
    (fun x _ => hf.differentiable (by simp) x) osc (mem_ball_self hδ) hb
  simp only [add_sub_cancel_left] at row
  exact row.trans (mul_le_mul_of_nonneg_left (h.norm_coe_le_norm s) hε.le)

private theorem smooth_order (K E : Type) [TopologicalSpace K] [CompactSpace K]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (n : ℕ) :
    ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F)
      (hf : ContDiff ℝ ∞ f), ContDiff ℝ n (ContinuousMap.comp (⟨f,hf.continuous⟩ : C(E,F)) :
        C(K,E) → C(K,F)) := by
  induction n with
  | zero =>
    intro F _ _ f hf
    exact contDiff_zero.mpr (ContinuousMap.continuous_postcomp _)
  | succ n ih =>
    intro F _ _ f hf
    apply contDiff_succ_iff_hasFDerivAt.mpr
    let df : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (m := ∞) (by simp)
    exact ⟨_,(evaluation (K := K) (E := E) (F := F)).contDiff.comp (ih _ _ df),derivative f hf⟩

theorem smooth (f : E → F) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (ContinuousMap.comp (⟨f,hf.continuous⟩ : C(E,F)) : C(K,E) → C(K,F)) :=
  contDiff_infty.mpr fun n => smooth_order K E n F f hf

end
end TransportOkaGrauert.SmoothPathComposition
