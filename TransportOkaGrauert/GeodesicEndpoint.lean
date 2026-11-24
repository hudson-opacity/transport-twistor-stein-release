import TransportOkaGrauert.ChartCorrespondence
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.Deriv.Prod

/-! # An omitted-boundary detector from nontrapping and conservation on actual geodesics -/
namespace TransportOkaGrauert.GeodesicEndpoint
noncomputable section
open Set Complex Metric ChartStein ChartCorrespondence SimpleDiskTarget
open scoped ContDiff Topology

/-- First time a continuous ray from the open disk meets the boundary. -/
theorem first_exit {z : ℝ → ℂ} {b : ℝ} (hb : 0 ≤ b) (hz : ContinuousOn z (Icc 0 b))
    (h0 : ‖z 0‖ < 1) (h1 : 1 ≤ ‖z b‖) :
    ∃ T ∈ Icc 0 b, ‖z T‖ = 1 ∧ ∀ t ∈ Ico 0 T, ‖z t‖ < 1 := by
  let S := Icc 0 b ∩ (fun t => ‖z t‖) ⁻¹' ({1} : Set ℝ)
  have reach (t : ℝ) (ht : t ∈ Icc 0 b) (hh : 1 ≤ ‖z t‖) :
      ∃ s ∈ Icc 0 t, ‖z s‖ = 1 := by
    exact intermediate_value_Icc ht.1 (hz.norm.mono (Icc_subset_Icc_right ht.2)) ⟨h0.le,hh⟩
  obtain ⟨s,hs,he⟩ := reach b (right_mem_Icc.mpr hb) h1
  have hclosed : IsClosed S := hz.norm.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hleast := (isCompact_Icc.of_isClosed_subset hclosed inter_subset_left).isLeast_sInf
    (show S.Nonempty from ⟨s,hs,he⟩)
  refine ⟨sInf S,hleast.1.1,hleast.1.2,?_⟩
  intro t ht
  by_contra! hn
  obtain ⟨r,hr,her⟩ := reach t ⟨ht.1,ht.2.le.trans hleast.1.1.2⟩ hn
  have hm := hleast.2 (show r ∈ S from ⟨⟨hr.1,hr.2.trans (ht.2.le.trans hleast.1.1.2)⟩,her⟩)
  exact (not_lt_of_ge hm) (hr.2.trans_lt ht.2)

private theorem trace_deriv {σ : ℂ → ℝ} {z : ℝ → ℂ} {θ : ℝ → ℝ} {S : Set ℝ}
    (ray : unitGeodesicOn σ z θ S) {t : ℝ} (ht : t ∈ S) {f : E → ℂ} (hf : ContDiff ℝ ∞ f) :
    HasDerivWithinAt (fun s => f (z s,(Circle.exp (θ s):ℂ)))
      ((Real.exp (-σ (z t)) : ℝ) • boundaryTransport σ f (z t) (Circle.exp (θ t))) S t := by
  let w := Circle.exp (θ t)
  let c := Real.exp (-σ (z t))
  let d := Isothermal.angularDrift σ (z t) w
  have ang : HasDerivAt (fun s : ℝ => (Circle.exp s : ℂ)) (I*(w:ℂ)) (θ t) := by
    simpa [w, Circle.coe_exp,mul_comm] using
      (((Complex.ofRealCLM.hasDerivAt (x := θ t)).mul_const I).cexp)
  have vel := ang.scomp_hasDerivWithinAt t (ray t ht).2
  have hdir : (((c:ℂ)*(w:ℂ)),(c*d) • (I*(w:ℂ))) = c • (((w:ℂ),(d:ℂ)*(I*(w:ℂ))):E) := by
    ext <;> simp [Complex.real_smul, mul_assoc]
  have pair : HasDerivWithinAt (fun s => (z s,(Circle.exp (θ s):ℂ)))
      (((c:ℂ)*(w:ℂ)),(c*d) • (I*(w:ℂ))) S t :=
    HasDerivWithinAt.prodMk (ray t ht).1 vel
  have h := (hf.differentiable (by simp) _).hasFDerivAt.comp_hasDerivWithinAt t pair
  change HasDerivWithinAt _ ((fderiv ℝ f (z t,(w:ℂ))) (((c:ℂ)*(w:ℂ)),(c*d) • (I*(w:ℂ)))) _ _ at h
  rw [hdir,map_smul] at h
  exact h

/-- Every unit direction over an interior base point lies on a conserved
zero divisor whose centre is on the base boundary. No separate geodesic
incidence or smooth dependence on the choice of exit point is needed. -/
theorem detector {σ : ℂ → ℝ} (simple : SimpleMetric σ) (F : ClosedDisk → E → ℂ)
    (smooth : ∀ a, ContDiff ℝ ∞ (F a))
    (conserved : ∀ a z, z ∈ ball (0:ℂ) 1 → ∀ v : Circle, boundaryTransport σ (F a) z v = 0)
    (centre : ∀ (a : ClosedDisk) (w : Circle), F a (a.val,w) = 0)
    (z₀ : ClosedDisk) (hz₀ : z₀.val ∈ ball (0:ℂ) 1) (w₀ : Circle) :
    ∃ a : ClosedDisk, ‖a.val‖ = 1 ∧ F a (z₀.val,w₀) = 0 := by
  obtain ⟨arg,ha⟩ : ∃ θ, Circle.exp θ = w₀ := ⟨_,Circle.exp_arg w₀⟩
  obtain ⟨i,b,z,θ,hi,hb,hz,hθ,ray,_,he⟩ := simple.escapes z₀.val z₀.property arg
  have sub : Icc 0 b ⊆ Icc i b := Icc_subset_Icc_left hi.le
  have cz : ContinuousOn z (Icc i b) := fun t ht => (ray t ht).1.continuousWithinAt
  have ca : ContinuousOn θ (Icc i b) := fun t ht => (ray t ht).2.continuousWithinAt
  obtain ⟨T,hT,h1,inside⟩ := first_exit hb.le (cz.mono sub) (hz ▸ mem_ball_zero_iff.mp hz₀) he.le
  let a : ClosedDisk := ⟨z T, mem_closedBall_zero_iff.mpr h1.le⟩
  let H (t : ℝ) := F a (z t,(Circle.exp (θ t):ℂ))
  have subT : Icc 0 T ⊆ Icc i b := Icc_subset_Icc hi.le hT.2
  have hcont : ContinuousOn H (Icc 0 T) := by
    apply (smooth a).continuous.comp_continuousOn
    exact (cz.mono subT).prodMk ((continuous_subtype_val.comp Circle.exp.continuous).comp_continuousOn (ca.mono subT))
  have hconst := constant_of_has_deriv_right_zero hcont (fun t ht => by
    have hh := trace_deriv ray (subT (mem_Icc_of_Ico ht)) (smooth a)
    rw [conserved a _ (mem_ball_zero_iff.mpr (inside t ht)), smul_zero] at hh
    exact (hh.mono subT).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht))
  have hval := (hconst T (right_mem_Icc.mpr hT.1)).symm.trans (centre a (Circle.exp (θ T)))
  simpa only [H, hz, hθ, ha] using (show ∃ a : ClosedDisk, ‖a.val‖ = 1 ∧
    F a (z 0,(Circle.exp (θ 0):ℂ)) = 0 from ⟨a,h1,hval⟩)

end
end TransportOkaGrauert.GeodesicEndpoint
