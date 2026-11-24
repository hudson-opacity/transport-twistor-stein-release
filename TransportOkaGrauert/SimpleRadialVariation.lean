import TransportOkaGrauert.ConformalFrame
import TransportOkaGrauert.SimpleRadialNormal
import TransportOkaGrauert.ChartJacobi
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! # Angular variation of the conformal geodesic flow

The conformal-frame brackets identify the normalized scalar Jacobi field
with the derivative of the actual flow under rotation of its initial velocity.
-/

noncomputable section
namespace TransportOkaGrauert.SimpleRadialVariation

open Complex Set Metric Filter VectorField ConformalFrame SimpleDiskTarget
open scoped ContDiff Topology

/-- Uniqueness for vector-valued linear ODEs with continuous coefficients on
a compact interval, including one-sided endpoint derivatives. -/
theorem linear_unique {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T : ℝ} {A : ℝ → E →L[ℝ] E} (hA : ContinuousOn A (Icc 0 T)) {u v : ℝ → E}
    (hu : ∀ t ∈ Icc 0 T, HasDerivWithinAt u (A t (u t)) (Icc 0 T) t)
    (hv : ∀ t ∈ Icc 0 T, HasDerivWithinAt v (A t (v t)) (Icc 0 T) t)
    (init : u 0 = v 0) : EqOn u v (Icc 0 T) := by
  obtain ⟨M, bound⟩ := isCompact_Icc.bddAbove_image hA.norm
  let C := Real.toNNReal M
  apply ODE_solution_unique_of_mem_Icc_right (v := fun t z => A t z) (s := fun _ => univ) (K := C)
  · intro t ht
    apply (A t).lipschitz.weaken (by
      change ‖A t‖₊ ≤ C
      exact_mod_cast (bound ⟨t,mem_Icc_of_Ico ht,rfl⟩).trans (Real.le_coe_toNNReal M)) |>.lipschitzOnWith
  · exact fun t ht => (hu t ht).continuousWithinAt
  · exact fun t ht => (hu t (mem_Icc_of_Ico ht)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)
  · exact fun _ _ => trivial
  · exact fun t ht => (hv t ht).continuousWithinAt
  · exact fun t ht => (hv t (mem_Icc_of_Ico ht)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)
  · exact fun _ _ => trivial
  · exact init

/-- The unique angular variation has horizontal coefficient the normalized
Jacobi field and vertical coefficient its arclength derivative. -/
theorem angular_variation {σ : ℂ → ℝ} (hs : ContDiff ℝ ∞ σ) {T : ℝ} (hT : 0 ≤ T)
    {p B : ℝ → Chart}
    (ray : ∀ t ∈ Icc 0 T, HasDerivWithinAt p (X σ (p t)) (Icc 0 T) t)
    (variational : ∀ t ∈ Icc 0 T, HasDerivWithinAt B (fderiv ℝ (X σ) (p t) (B t)) (Icc 0 T) t)
    (initial : B 0 = V (p 0)) :
    ∃ j dj, jacobiOn σ (fun t => (p t).1) j dj (Icc 0 T) ∧ j 0 = 0 ∧ dj 0 = 1 ∧
      ∀ t ∈ Icc 0 T, B t = j t • H σ (p t) + dj t • V (p t) := by
  have cp : ContinuousOn p (Icc 0 T) := fun t ht => (ray t ht).continuousWithinAt
  let k : C(Icc 0 T, ℝ) := ⟨fun t => curvature σ (p t).1,
    (ChartJacobi.curvature_contDiff hs).continuous.comp (continuous_fst.comp cp.restrict)⟩
  let j := ChartJacobi.field hT k
  let dj := ChartJacobi.speed hT k
  have ode : jacobiOn σ (fun t => (p t).1) j dj (Icc 0 T) := ChartJacobi.solves hT k
  obtain ⟨z, one⟩ := ChartJacobi.initial_values hT k
  have h0 : j 0 = 0 := z
  have h1 : dj 0 = 1 := one
  refine ⟨j,dj,ode,h0,h1,?_⟩
  obtain ⟨hX,hH⟩ := smooth_XH hs
  apply linear_unique ((hX.fderiv_right (m := ∞) (by simp)).continuous.comp_continuousOn cp) variational
  · intro t ht
    have dH := (hH.differentiable (by simp) (p t)).hasFDerivAt.comp_hasDerivWithinAt t (ray t ht)
    have dV : HasDerivWithinAt (fun s => V (p s)) 0 (Icc 0 T) t := hasDerivWithinAt_const ..
    have h := (((ode t ht).1).smul dH).add (((ode t ht).2).smul dV)
    have b := brackets hs (p t)
    have bH := b.2.2.1
    have bV := b.1
    change fderiv ℝ (H σ) (p t) (X σ (p t)) - fderiv ℝ (X σ) (p t) (H σ (p t)) =
      curvature σ (p t).1 • V (p t) at bH
    change fderiv ℝ (X σ) (p t) (V (p t)) - fderiv ℝ V (p t) (X σ (p t)) = H σ (p t) at bV
    rw [show fderiv ℝ V (p t) = 0 from fderiv_const_apply .., ContinuousLinearMap.zero_apply,
      sub_zero] at bV
    convert h using 1
    simp only [Function.comp_apply, map_add, map_smul, bV, sub_eq_iff_eq_add.mp bH,
      smul_add, smul_smul, smul_zero, zero_add, neg_mul, neg_smul]
    rw [mul_comm (curvature σ (p t).1) (j t)]
    abel
  · simpa [h0,h1] using initial

/-- Differentiating a smooth two-parameter family of integral curves in its
initial parameter produces a solution of the linearized equation. -/
theorem differentiated_flow {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : (ℝ × ℝ) → E} {X : E → E} {a t : ℝ} (hf : ContDiffAt ℝ ∞ F (a,t))
    (hx : DifferentiableAt ℝ X (F (a,t)))
    (ode : (fun q => fderiv ℝ F q (0,1)) =ᶠ[𝓝 (a,t)] X ∘ F) :
    HasDerivAt (fun s => fderiv ℝ F (a,s) (1,0))
      (fderiv ℝ X (F (a,t)) (fderiv ℝ F (a,t) (1,0))) t := by
  let q := (a,t)
  let u : ℝ × ℝ := (1,0)
  let v : ℝ × ℝ := (0,1)
  have D := ((hf.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)).hasFDerivAt
  have direction (b : ℝ × ℝ) := D.clm_apply (hasFDerivAt_const b q)
  have line : HasDerivAt (fun s => (a,s)) v t := (hasDerivAt_const t a).prodMk (hasDerivAt_id t)
  have h := (direction u).comp_hasDerivAt t line
  have sym := hf.isSymmSndFDerivAt (by simpa using (show (2 : WithTop ℕ∞) ≤ ∞ from by decide)) v u
  have rhs := hx.hasFDerivAt.comp q ((hf.differentiableAt (by simp)).hasFDerivAt)
  have eqn := DFunLike.congr_fun (ode.fderiv_eq (𝕜 := ℝ)) u
  rw [(direction v).fderiv, rhs.fderiv] at eqn
  simpa [q] using (show HasDerivAt (fun s => fderiv ℝ F (a,s) u)
    (fderiv ℝ X (F q) (fderiv ℝ F q u)) t from by
    convert h using 1
    simpa [q, ContinuousLinearMap.comp_apply, ← sym] using eqn.symm)

private theorem circle_unit (a : ℝ) : unit a = (Circle.exp a : ℂ) := by
  apply Complex.ext <;> simp [unit, Complex.real_smul, -Complex.ofReal_cos, -Complex.ofReal_sin]

theorem circle_normal (a : ℝ) : normal a = I * (Circle.exp a : ℂ) := by
  apply Complex.ext <;> simp [normal, Complex.real_smul, -Complex.ofReal_cos, -Complex.ofReal_sin]

theorem chart_columns (σ : ℂ → ℝ) (p : Chart) :
    X σ p = (↑(Real.exp (-σ p.1)) * (Circle.exp p.2.1 : ℂ),
      Real.exp (-σ p.1) * Isothermal.angularDrift σ p.1 (Circle.exp p.2.1), 0) ∧
    (H σ p).1 = Real.exp (-σ p.1) • (I * (Circle.exp p.2.1 : ℂ)) := by
  constructor
  · change (_, _, _) = _
    congr 1
    · change Real.exp (-σ p.1) • unit p.2.1 = _
      rw [circle_unit, Complex.real_smul]
    · change (_, _) = _
      congr 1
      change Real.exp (-σ p.1) * fderiv ℝ σ p.1 (normal p.2.1) = _
      congr 1
      simp only [normal, Isothermal.angularDrift, map_add, map_smul, smul_eq_mul,
        Circle.coe_exp, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
      ring
  · change _ • normal _ = _
    rw [circle_normal]
    rfl

/-- For an actual smooth angular family of geodesics, angular differentiation
gives the normalized normal Jacobi field along its central ray. The flow
equation need only hold in a neighborhood of this finite segment. -/
theorem jacobi_of_flow {σ : ℂ → ℝ} (hs : ContDiff ℝ ∞ σ) {T α : ℝ} (hT : 0 ≤ T)
    (F : (ℝ × ℝ) → Chart) (smooth : ∀ t ∈ Icc 0 T, ContDiffAt ℝ ∞ F (α,t))
    (ode : ∀ t ∈ Icc 0 T, (fun q => fderiv ℝ F q (0,1)) =ᶠ[𝓝 (α,t)] X σ ∘ F)
    (initial : fderiv ℝ F (α,0) (1,0) = V (F (α,0))) :
    let z := fun t => (F (α,t)).1
    let θ := fun t => (F (α,t)).2.1
    unitGeodesicOn σ z θ (Icc 0 T) ∧ ∃ j dj, jacobiOn σ z j dj (Icc 0 T) ∧
      j 0 = 0 ∧ dj 0 = 1 ∧ ∀ t ∈ Icc 0 T,
      (fderiv ℝ F (α,t) (1,0)).1 = (j t * Real.exp (-σ (z t))) • (I * (Circle.exp (θ t) : ℂ)) := by
  intro z θ
  let p := fun t => F (α,t)
  let B := fun t => fderiv ℝ F (α,t) (1,0)
  have hX := (smooth_XH hs).1
  have ray (t : ℝ) (ht : t ∈ Icc 0 T) : HasDerivAt p (X σ (p t)) t := by
    have line : HasDerivAt (fun s => (α,s)) ((0,1) : ℝ × ℝ) t :=
      (hasDerivAt_const t α).prodMk (hasDerivAt_id t)
    have eq : fderiv ℝ F (α,t) (0,1) = X σ (p t) := (ode t ht).self_of_nhds
    rw [← eq]
    exact ((smooth t ht).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t line
  constructor
  · intro t ht
    have d := (ray t ht).hasDerivWithinAt (s := Icc 0 T)
    rw [(chart_columns σ (p t)).1] at d
    exact ⟨(ContinuousLinearMap.fst ℝ ℂ (ℝ × ℝ)).hasFDerivAt.comp_hasDerivWithinAt t d,
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (.snd ℝ ℂ (ℝ × ℝ))).hasFDerivAt.comp_hasDerivWithinAt t d⟩
  obtain ⟨j,dj,oj,h0,h1,formula⟩ := angular_variation hs hT
    (fun t ht => (ray t ht).hasDerivWithinAt)
    (fun t ht => (differentiated_flow (smooth t ht) (hX.differentiable (by simp) _) (ode t ht)).hasDerivWithinAt)
    initial
  refine ⟨j,dj,oj,h0,h1,fun t ht => ?_⟩
  have base := congrArg Prod.fst (formula t ht)
  simpa [Prod.smul_mk, V, (chart_columns σ (p t)).2, smul_smul, p, z, θ, mul_assoc] using base

private theorem smooth_unique {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {X : E → E} (hX : ContDiff ℝ ∞ X) {T : ℝ} {p q : ℝ → E}
    (p' : ∀ t ∈ Icc 0 T, HasDerivWithinAt p (X (p t)) (Icc 0 T) t)
    (q' : ∀ t ∈ Icc 0 T, HasDerivWithinAt q (X (q t)) (Icc 0 T) t)
    (h0 : p 0 = q 0) : EqOn p q (Icc 0 T) := by
  have pc : ContinuousOn p (Icc 0 T) := fun t ht => (p' t ht).continuousWithinAt
  have qc : ContinuousOn q (Icc 0 T) := fun t ht => (q' t ht).continuousWithinAt
  let S := p '' Icc 0 T ∪ q '' Icc 0 T
  have compact : IsCompact S := (isCompact_Icc.image_of_continuousOn pc).union
    (isCompact_Icc.image_of_continuousOn qc)
  obtain ⟨K, lip⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact compact
    ((hX.of_le (show (1 : WithTop ℕ∞) ≤ ∞ by decide)).locallyLipschitz.locallyLipschitzOn (s := S))
  exact ODE_solution_unique_of_mem_Icc_right (v := fun _ => X) (s := fun _ => S) (fun _ _ => lip) pc
    (fun t ht => (p' t (mem_Icc_of_Ico ht)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht))
    (fun t ht => Or.inl ⟨_,mem_Icc_of_Ico ht,rfl⟩) qc
    (fun t ht => (q' t (mem_Icc_of_Ico ht)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht))
    (fun t ht => Or.inr ⟨_,mem_Icc_of_Ico ht,rfl⟩) h0

theorem polar_angle (x : ℂ) : ‖x‖ • (Circle.exp x.arg : ℂ) = x := by
  simpa only [Complex.real_smul, Circle.coe_exp] using norm_mul_exp_arg_mul_I x

theorem angle_velocity (a : ℝ) :
    HasDerivAt (fun s => (Circle.exp s : ℂ)) (I * (Circle.exp a : ℂ)) a := by
  simpa [Circle.coe_exp, mul_comm] using (((Complex.ofRealCLM.hasDerivAt (x := a)).mul_const I).cexp)

/-- A smooth endpoint map in Cartesian initial velocity and its lifted polar
geodesic flow suffice for a smooth inverse on the entire open base disk.
All geometric hypotheses (escape, strict boundary convexity and no conjugate
points) come from the single chart definition of simplicity. The vector field
can be smoothly modified away from the closed unit disk to make it complete. -/
theorem smooth_log_of_geodesic_flow {σ : ℂ → ℝ} (simple : SimpleMetric σ)
    (f : ℂ → ℂ) (F : (ℝ × ℝ) → Chart)
    (smooth : ContDiff ℝ ∞ f) (smoothF : ContDiff ℝ ∞ F)
    (centre : ‖f 0‖ < 1)
    (initial : ∀ α : ℝ, F (α,0) = (f 0,α,0))
    (projection : ∀ α t : ℝ, (F (α,t)).1 = f (t • (Circle.exp α : ℂ)))
    (ode : ∀ q : ℝ × ℝ, ‖(F q).1‖ ≤ 1 →
      (fun u => fderiv ℝ F u (0,1)) =ᶠ[𝓝 q] X σ ∘ F) :
    ∃ L : ℂ → ℂ, ContDiffOn ℝ ∞ L (ball (0 : ℂ) 1) ∧
      (∀ y ∈ ball (0 : ℂ) 1, L y ∈ SimpleRadialStar.retained f 1 ∧ f (L y) = y) ∧
      ∀ x ∈ SimpleRadialStar.retained f 1, f x ∈ ball (0 : ℂ) 1 → L (f x) = x := by
  have flow (α t : ℝ) (ht : ‖(F (α,t)).1‖ ≤ 1) :
      HasDerivAt (fun s => F (α,s)) (X σ (F (α,t))) t := by
    have h : fderiv ℝ F (α,t) (0,1) = X σ (F (α,t)) := (ode _ ht).self_of_nhds
    rw [← h]
    exact (smoothF.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_const t α).prodMk (hasDerivAt_id t))
  have start (α : ℝ) : fderiv ℝ F (α,0) (1,0) = V (F (α,0)) := by
    have line : HasDerivAt (fun s : ℝ => (s,(0 : ℝ))) (1,0) α :=
      (hasDerivAt_id α).prodMk (hasDerivAt_const α 0)
    have actual := (smoothF.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt α line
    have wanted := (hasDerivAt_const α (f 0)).prodMk ((hasDerivAt_id α).prodMk (hasDerivAt_const α (0 : ℝ)))
    exact actual.unique (wanted.congr_of_eventuallyEq (.of_forall initial))
  apply SimpleRadialNormal.smooth_log_of_jacobi_variation simple f smooth.continuous centre
  · intro w
    let α := (w : ℂ).arg
    have ew : Circle.exp α = w := Circle.exp_arg w
    obtain ⟨a,b,z,θ,ha,hb,hz,hθ,geo,_,outside⟩ :=
      simple.escapes _ (mem_closedBall_zero_iff.mpr centre.le) α
    by_contra! stays
    have hit (t : ℝ) (ht : t ∈ Icc 0 b) : ‖(F (α,t)).1‖ ≤ 1 := by
      rcases eq_or_lt_of_le ht.1 with h | h
      · simp [← h, initial, centre.le]
      · rw [projection, ew]; exact stays t h
    let p (t : ℝ) : Chart := (z t,θ t,0)
    have sub : Icc 0 b ⊆ Icc a b := Icc_subset_Icc_left ha.le
    have du (t : ℝ) (ht : t ∈ Icc 0 b) : HasDerivWithinAt p (X σ (p t)) (Icc 0 b) t := by
      rw [(chart_columns σ (p t)).1]
      exact ((geo t (sub ht)).1.prodMk ((geo t (sub ht)).2.prodMk
        (hasDerivWithinAt_const t (Icc a b) (0 : ℝ)))).mono sub
    have eq := smooth_unique (smooth_XH simple.smooth).1
      (fun t ht => (flow α t (hit t ht)).hasDerivWithinAt) du (by simp [initial,p,hz,hθ])
    have atB := congrArg Prod.fst (eq (right_mem_Icc.mpr hb.le))
    exact (not_lt_of_ge (hit b (right_mem_Icc.mpr hb.le))) (atB ▸ outside)
  · exact fun _ _ => smooth.contDiffAt
  · let c := Real.exp (-σ (f 0))
    have radial (α : ℝ) : fderiv ℝ f 0 (Circle.exp α : ℂ) = c • (Circle.exp α : ℂ) := by
      have h := flow α 0 (by simp [initial, centre.le])
      have hbase := (ContinuousLinearMap.fst ℝ ℂ (ℝ × ℝ)).hasFDerivAt.comp_hasDerivAt 0 h
      have actual := (smooth.differentiable (by simp) ((0:ℝ) • (Circle.exp α : ℂ))).hasFDerivAt.comp_hasDerivAt
        0 ((hasDerivAt_id (0 : ℝ)).smul_const (Circle.exp α : ℂ))
      have same := actual.unique (hbase.congr_of_eventuallyEq (.of_forall (fun s => (projection α s).symm)))
      change fderiv ℝ f ((0:ℝ) • (Circle.exp α : ℂ)) ((1:ℝ) • (Circle.exp α : ℂ)) =
        (X σ (F (α,0))).1 at same
      rw [(chart_columns σ (F (α,0))).1, initial] at same
      simpa only [zero_smul, one_smul, c, Complex.real_smul] using same
    have all (x : ℂ) : fderiv ℝ f 0 x = c • x := by
      conv_lhs => arg 2; rw [← polar_angle x]
      rw [map_smul, radial, smul_comm, polar_angle]
    have hn : c ≠ 0 := Real.exp_ne_zero _
    constructor
    · intro u v eq
      rw [all, all] at eq
      exact (smul_right_injective _ hn) eq
    · intro u
      exact ⟨c⁻¹ • u, by rw [all, smul_inv_smul₀ hn]⟩
  · intro x hx hx0
    let α := x.arg
    let r := ‖x‖
    have hp : 0 < r := norm_pos_iff.mpr hx0
    have repr (t : ℝ) : SimpleRadialStar.along f x t = (F (α,t)).1 := by
      rw [projection]
      change f ((t/r) • x) = _
      calc
        _ = f ((t/r) • (r • (Circle.exp α : ℂ))) := by rw [polar_angle x]
        _ = _ := by rw [smul_smul, div_mul_cancel₀ _ hp.ne']
    have inDisk (t : ℝ) (ht : t ∈ Icc 0 r) : ‖(F (α,t)).1‖ ≤ 1 := by
      rw [← repr]; exact mem_closedBall_zero_iff.mp (SimpleRadialStar.along_retained hx0 hx t ht)
    obtain ⟨ge,j,dj,oj,j0,j1,atTime⟩ := jacobi_of_flow simple.smooth hp.le F
      (fun _ _ => smoothF.contDiffAt) (fun t ht => ode _ (inDisk t ht)) (start α)
    have alongEq := funext repr
    refine ⟨fun t => (F (α,t)).2.1, alongEq ▸ ge, j, dj, alongEq ▸ oj, j0, j1,?_⟩
    have line : HasDerivAt (fun s : ℝ => (s,r)) (1,0) α := (hasDerivAt_id α).prodMk (hasDerivAt_const α r)
    have base := (ContinuousLinearMap.fst ℝ ℂ (ℝ × ℝ)).hasFDerivAt.comp_hasDerivAt α
      ((smoothF.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt α line)
    have alongα := (smooth.differentiable (by simp) (r • (Circle.exp α : ℂ))).hasFDerivAt.comp_hasDerivAt α
      ((angle_velocity α).const_smul r)
    have actual := alongα.unique (base.congr_of_eventuallyEq (.of_forall (fun s => (projection s r).symm)))
    have atR : (F (α,r)).1 = f x := by rw [projection, polar_angle]
    have hv : r • (I * (Circle.exp α : ℂ)) = I*x := by rw [← mul_smul_comm, polar_angle]
    rw [show r • (Circle.exp α : ℂ) = x from polar_angle x,hv] at actual
    exact actual.trans (by simpa only [atR] using atTime r (right_mem_Icc.mpr hp.le))

end TransportOkaGrauert.SimpleRadialVariation
