import TransportOkaGrauert.ScalarGeneralFlow
import TransportOkaGrauert.GlobalGeodesicFlow
import TransportOkaGrauert.PencilLifts

/-! The unattenuated scalar directional equation has a globally smooth
unrestricted angular solution on every simple chart disk. -/
noncomputable section
namespace TransportOkaGrauert.ScalarGeneralUnrestricted
open Complex Set Metric Filter SimpleDiskTarget PathContinuation ScalarGeneralFlow GeodesicFlowExtension
open scoped Topology ContDiff

/-- Two integral curves of a smooth field on a compact time interval agree
throughout when they agree at either endpoint. -/
theorem endpoint_unique {X : State → State} (hX : ContDiff ℝ ∞ X) {f g : ℝ → State}
    {a b : ℝ} (df : ∀ t ∈ Icc a b, HasDerivWithinAt f (X (f t)) (Icc a b) t)
    (dg : ∀ t ∈ Icc a b, HasDerivWithinAt g (X (g t)) (Icc a b) t)
    (same : f a = g a ∨ f b = g b) : EqOn f g (Icc a b) := by
  have cf : ContinuousOn f (Icc a b) := fun t ht => (df t ht).continuousWithinAt
  have cg : ContinuousOn g (Icc a b) := fun t ht => (dg t ht).continuousWithinAt
  obtain ⟨R,hR⟩ := ((isCompact_Icc.image_of_continuousOn cf).union
    (isCompact_Icc.image_of_continuousOn cg)).isBounded.subset_closedBall (0:State)
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0:State) R).bddAbove_image
    (hX.continuous_fderiv (by simp)).nnnorm.continuousOn
  have L : LipschitzOnWith C X (closedBall (0:State) R) :=
    Convex.lipschitzOnWith_of_nnnorm_fderiv_le (fun p _ => hX.differentiable (by simp) p)
      (fun p hp => hC ⟨p,hp,rfl⟩) (convex_closedBall _ _)
  have hf (t : ℝ) (ht : t ∈ Icc a b) := hR (Or.inl (mem_image_of_mem f ht))
  have hg (t : ℝ) (ht : t ∈ Icc a b) := hR (Or.inr (mem_image_of_mem g ht))
  rcases same with h | h
  · exact ODE_solution_unique_of_mem_Icc_right (v := fun _ => X) (s := fun _ => closedBall (0:State) R)
      (fun _ _ => L) cf (fun t ht => (df t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht))
      (fun t ht => hf t (Ico_subset_Icc_self ht)) cg
      (fun t ht => (dg t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht))
      (fun t ht => hg t (Ico_subset_Icc_self ht)) h
  · exact ODE_solution_unique_of_mem_Icc_left (v := fun _ => X) (s := fun _ => closedBall (0:State) R)
      (fun _ _ => L) cf (fun t ht => (df t (Ioc_subset_Icc_self ht)).mono_of_mem_nhdsWithin (Icc_mem_nhdsLE_of_mem ht))
      (fun t ht => hf t (Ioc_subset_Icc_self ht)) cg
      (fun t ht => (dg t (Ioc_subset_Icc_self ht)).mono_of_mem_nhdsWithin (Icc_mem_nhdsLE_of_mem ht))
      (fun t ht => hg t (Ioc_subset_Icc_self ht)) h

private theorem ray_deriv {σ z θ S} (ray : unitGeodesicOn σ z θ S) {t : ℝ} (ht : t ∈ S) :
    HasDerivWithinAt (fun r => (z r,θ r)) (chartVector σ (z t,θ t)) S t :=
  (ray t ht).1.prodMk (ray t ht).2

/-- Any complete curve which solves the original geodesic ODE whenever its
base is in the closed disk must escape backwards. The extension may have any
behavior after exit. -/
theorem backward_escape {σ : ℂ → ℝ} (simple : SimpleMetric σ) (γ : ℝ → State)
    (h0 : (γ 0).1 ∈ closedBall (0:ℂ) 1)
    (D : ∀ t, (γ t).1 ∈ closedBall (0:ℂ) 1 → HasDerivAt γ (chartVector σ (γ t)) t) :
    ∃ s : ℝ, 0 < s ∧ 1 < ‖(γ (-s)).1‖ := by
  by_contra! lock
  have inside (t : ℝ) (ht : t ≤ 0) : (γ t).1 ∈ closedBall (0:ℂ) 1 := by
    rcases ht.eq_or_lt with rfl | ht
    · exact h0
    · exact mem_closedBall_zero_iff.mpr (by simpa using lock (-t) (neg_pos.mpr ht))
  obtain ⟨a,b,z,θ,ha,hb,hz,hθ,ray,exit,_⟩ := simple.escapes _ h0 (γ 0).2
  have sub : Icc a 0 ⊆ Icc a b := Icc_subset_Icc_right hb.le
  have smooth : ContDiff ℝ ∞ (chartVector σ) := contDiff_iff_contDiffAt.mpr fun p =>
    ChartRegularity.chartVector_contDiffAt p simple.smooth.contDiffAt
  have eq := endpoint_unique smooth (a := a) (b := 0)
    (fun t ht => (D t (inside t ht.2)).hasDerivWithinAt)
    (fun t ht => (ray_deriv ray (sub ht)).mono sub) (Or.inr (by simp [hz,hθ]))
  have e := congrArg Prod.fst (eq (x := a) (left_mem_Icc.mpr ha.le))
  exact (not_lt_of_ge (mem_closedBall_zero_iff.mp (inside a ha.le))) (e ▸ exit)

/-- Forward version of `backward_escape`. -/
theorem forward_escape {σ : ℂ → ℝ} (simple : SimpleMetric σ) (γ : ℝ → State)
    (h0 : (γ 0).1 ∈ closedBall (0:ℂ) 1)
    (D : ∀ t, (γ t).1 ∈ closedBall (0:ℂ) 1 → HasDerivAt γ (chartVector σ (γ t)) t) :
    ∃ s : ℝ, 0 < s ∧ 1 < ‖(γ s).1‖ := by
  by_contra! lock
  have inside (t : ℝ) (ht : 0 ≤ t) : (γ t).1 ∈ closedBall (0:ℂ) 1 := by
    rcases ht.eq_or_lt with rfl | ht
    · exact h0
    · exact mem_closedBall_zero_iff.mpr (lock t ht)
  obtain ⟨a,b,z,θ,ha,hb,hz,hθ,ray,_,exit⟩ := simple.escapes _ h0 (γ 0).2
  have sub : Icc 0 b ⊆ Icc a b := Icc_subset_Icc_left ha.le
  have smooth : ContDiff ℝ ∞ (chartVector σ) := contDiff_iff_contDiffAt.mpr fun p =>
    ChartRegularity.chartVector_contDiffAt p simple.smooth.contDiffAt
  have eq := endpoint_unique smooth (a := 0) (b := b)
    (fun t ht => (D t (inside t ht.1)).hasDerivWithinAt)
    (fun t ht => (ray_deriv ray (sub ht)).mono sub) (Or.inl (by simp [hz,hθ]))
  have e := congrArg Prod.fst (eq (x := b) (right_mem_Icc.mpr hb.le))
  exact (not_lt_of_ge (mem_closedBall_zero_iff.mp (inside b hb.le))) (e ▸ exit)

end TransportOkaGrauert.ScalarGeneralUnrestricted
