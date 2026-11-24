import TransportOkaGrauert.NormalFredholm
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-! # The Fredholm alternative for the asymmetric order-zero reduction

Conjugating a positive geodesic normal operator by a reference inverse
on one side need not preserve self-adjointness. Compact perturbations on
a Hilbert space admit a finite-rank approximation in operator norm. This
gives surjectivity from injectivity for the conjugated operator. -/
namespace TransportOkaGrauert.NormalFredholm
noncomputable section
open Set Metric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
private theorem finite_correction (S : E →ₗ[ℝ] E) (V : Submodule ℝ E) [FiniteDimensional ℝ V]
    (land : ∀ x, S x ∈ V) (inj : Function.Injective ((LinearMap.id : E →ₗ[ℝ] E) + S)) :
    Function.Surjective ((LinearMap.id : E →ₗ[ℝ] E) + S) := by
  let T := (LinearMap.id : E →ₗ[ℝ] E) + S
  let A : V →ₗ[ℝ] V := T.restrict (fun x hx => V.add_mem hx (land x))
  have ai : Function.Injective A := fun x y eq => Subtype.ext (inj (congrArg Subtype.val eq))
  intro y
  obtain ⟨v,hv⟩ := LinearMap.surjective_of_injective ai (⟨S y,land y⟩ : V)
  have eq : T (v:E) = S y := congrArg Subtype.val hv
  refine ⟨y-v,?_⟩
  change T (y-v) = y
  rw [map_sub,eq]
  simp [T]

omit [CompleteSpace E] in
theorem approximate (K : E →L[ℝ] E) (compact : ∃ C : Set E, IsCompact C ∧ K '' closedBall 0 1 ⊆ C)
    {ε : ℝ} (he : 0 < ε) :
    ∃ (S : E →L[ℝ] E) (V : Submodule ℝ E), FiniteDimensional ℝ V ∧
      (∀ x, S x ∈ V) ∧ ‖K-S‖ ≤ ε := by
  obtain ⟨C,hC,image⟩ := compact
  obtain ⟨points,_,fin,covers⟩ := hC.finite_cover_balls he
  let V := Submodule.span ℝ points
  haveI : FiniteDimensional ℝ V := FiniteDimensional.span_of_finite ℝ fin
  let S : E →L[ℝ] E := V.starProjection.comp K
  have range (x : E) : S x ∈ V := (V.orthogonalProjection (K x)).property
  refine ⟨S,V,inferInstance,range,(K-S).opNorm_le_bound he.le (fun x => ?_)⟩
  by_cases hx : x = 0
  · simp [hx]
  have xPos := norm_pos_iff.mpr hx
  let u := (‖x‖⁻¹ : ℝ) • x
  have hu : ‖u‖ = 1 := by
    simp [u,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr xPos.le),xPos.ne']
  obtain ⟨y,hy⟩ := mem_iUnion.mp (covers (image ⟨u,mem_closedBall_zero_iff.mpr hu.le,rfl⟩))
  obtain ⟨py,near⟩ := mem_iUnion.mp hy
  have yV : y ∈ V := Submodule.subset_span py
  have lb : BddBelow (Set.range (fun v : V => ‖K u - (v:E)‖)) :=
    ⟨0,by rintro _ ⟨v,rfl⟩; exact norm_nonneg _⟩
  have bound : ‖(K-S) u‖ ≤ ε := calc
    _ = ⨅ v : V, ‖K u - (v:E)‖ := Submodule.starProjection_minimal _
    _ ≤ ‖K u-y‖ := ciInf_le lb (⟨y,yV⟩ : V)
    _ ≤ ε := by simpa [dist_eq_norm] using (mem_ball.mp near).le
  change ‖(K-S) ((‖x‖⁻¹ : ℝ) • x)‖ ≤ ε at bound
  rw [map_smul,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr xPos.le),←div_eq_inv_mul] at bound
  exact (div_le_iff₀ xPos).mp bound

/-- No symmetry is needed after conjugation by the reference inverse. -/
theorem compact_alternative (K : E →L[ℝ] E)
    (compact : ∃ C : Set E, IsCompact C ∧ K '' closedBall 0 1 ⊆ C)
    (inj : Function.Injective (ContinuousLinearMap.id ℝ E + K)) :
    Function.Surjective (ContinuousLinearMap.id ℝ E + K) := by
  obtain ⟨S,V,finite,land,near⟩ := approximate K compact (ε := 1/2) (by norm_num)
  letI := finite
  let R := K-S
  let A : E →L[ℝ] E := 1+R
  have hR : ‖-R‖ < 1 := by rw [norm_neg]; exact near.trans_lt (by norm_num)
  have au : IsUnit A := by
    simpa [A,sub_neg_eq_add] using (Units.oneSub (-R) hR).isUnit
  have bij := ContinuousLinearMap.isUnit_iff_bijective.mp au
  let e := ContinuousLinearEquiv.ofBijective A (LinearMap.ker_eq_bot.mpr bij.1) (LinearMap.range_eq_top.mpr bij.2)
  let W : E →ₗ[ℝ] E := S.toLinearMap.comp e.symm.toLinearEquiv.toLinearMap
  let T := ContinuousLinearMap.id ℝ E + K
  have decomp (x : E) : A x + S x = T x := by simp [A,R,T]; abel
  have normed (x : E) : ((LinearMap.id : E →ₗ[ℝ] E) + W) x = T (e.symm x) := by
    change x + S (e.symm x) = _
    rw [← decomp,show A (e.symm x) = x from e.apply_symm_apply x]
  have iw : Function.Injective ((LinearMap.id : E →ₗ[ℝ] E) + W) := by
    intro x y h
    rw [normed,normed] at h
    exact e.symm.injective (inj h)
  have onto := finite_correction W V (fun x => land _) iw
  intro y
  obtain ⟨x,hx⟩ := onto y
  exact ⟨e.symm x,(normed x).symm.trans hx⟩

/-- A smoothing remainder and dense attainable data suffice to solve the
smooth range problem exactly. The sole orthogonality test is on smooth
vectors because the adjoint remainder smooths every Hilbert vector. -/
theorem smooth_range (S D : Submodule ℝ E) (inside : D ≤ S) (dense : Dense (S : Set E))
    (K : E →L[ℝ] E) (compact : ∃ C : Set E, IsCompact C ∧ K '' closedBall 0 1 ⊆ C)
    (reg : ∀ x, K x ∈ S) (adjReg : ∀ x, K.adjoint x ∈ S)
    (approxSol : ∀ x ∈ S, x + K x ∈ D) (uniq : ∀ x ∈ S, x ∈ Dᗮ → x = 0) :
    D = S := by
  let T := ContinuousLinearMap.id ℝ E + K
  have orth : Dᗮ = ⊥ := by
    apply bot_unique
    intro y hy
    have test (x : E) : inner ℝ x (y + K.adjoint y) = 0 := by
      have closed : IsClosed {z : E | inner ℝ z (y+K.adjoint y) = 0} :=
        isClosed_eq (continuous_id.inner continuous_const) continuous_const
      apply (closure_minimal _ closed) (dense x)
      intro z hz
      change inner ℝ z (y+K.adjoint y) = 0
      rw [inner_add_right,K.adjoint_inner_right,← inner_add_left]
      exact hy _ (approxSol z hz)
    have eq := inner_self_eq_zero (𝕜 := ℝ) |>.mp (test (y+K.adjoint y))
    have sy := S.neg_mem (adjReg y)
    have ys : y ∈ S := (eq_neg_of_add_eq_zero_left eq).symm ▸ sy
    exact (uniq _ ys hy : y = 0)
  have dD : Dense (D : Set E) := by
    haveI := D.isClosed_topologicalClosure.completeSpace_coe
    have top := (D.topologicalClosure.orthogonal_eq_bot_iff).mp (D.orthogonal_closure.trans orth)
    intro x
    change x ∈ D.topologicalClosure
    rw [top]; trivial
  obtain ⟨P,V,finite,land,near⟩ := approximate K compact (ε := 1/2) (by norm_num)
  letI := finite
  let R := K-P
  let A : E →L[ℝ] E := 1+R
  have hR : ‖-R‖ < 1 := by rw [norm_neg]; exact near.trans_lt (by norm_num)
  have au : IsUnit A := by simpa [A,sub_neg_eq_add] using (Units.oneSub (-R) hR).isUnit
  have bij := ContinuousLinearMap.isUnit_iff_bijective.mp au
  let e := ContinuousLinearEquiv.ofBijective A (LinearMap.ker_eq_bot.mpr bij.1) (LinearMap.range_eq_top.mpr bij.2)
  let W := P.comp e.symm.toContinuousLinearMap
  let V' := D.map W.toLinearMap
  haveI : FiniteDimensional ℝ V' := Submodule.finiteDimensional_of_le
    (show V' ≤ V by rintro _ ⟨x,_,rfl⟩; exact land _)
  have closed := V'.closed_of_finiteDimensional
  apply le_antisymm inside
  intro f sf
  have mem : W f ∈ V' := by
    apply (closure_minimal _ (closed.preimage W.continuous)) (dD f)
    intro v hv
    exact ⟨v,hv,rfl⟩
  obtain ⟨d,hd,eq⟩ := mem
  let x := e.symm (f-d)
  have zero : P x = 0 := by
    change W (f-d) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr eq.symm
  have decomp : x + K x = f-d := calc
    _ = A x + P x := by simp [A,R]; abel
    _ = f-d := by rw [zero,add_zero]; exact e.apply_symm_apply _
  have sx : x ∈ S := by
    have eqx : x = (f-d) - K x := by rw [← decomp]; abel
    rw [eqx]; exact S.sub_mem (S.sub_mem sf (inside hd)) (reg x)
  have solved := D.add_mem (approxSol x sx) hd
  rwa [decomp,sub_add_cancel] at solved

end
end TransportOkaGrauert.NormalFredholm
