import TransportOkaGrauert.SimpleRadialVariation
import TransportOkaGrauert.GlobalGeodesicFlow
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-! # Smooth Cartesian construction of the geodesic endpoint

The direction parameter is a Cartesian vector, including zero. The evolving
angle is the change relative to the initial frame. Both the position and this
rotation have an ODE homogeneous in the direction parameter on the unit
parameter ball. Evaluating the bounded-parameter flow at a smoothly rescaled
time avoids polar coordinates through the centre.
-/

noncomputable section
namespace TransportOkaGrauert.SimpleRadialSpray

open Complex Metric Set Filter ConformalFrame
open scoped ContDiff Topology NNReal

abbrev State := ℂ × ℂ × ℝ
private abbrev Cartesian := ℂ × ℂ × ℂ

private def cutoff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [HasContDiffBump E] : ContDiffBump (0 : E) := ⟨2,3,by norm_num,by norm_num⟩

private def rotate (θ : ℝ) : ℂ := Circle.exp θ

private theorem rotation_smooth : ContDiff ℝ ∞ rotate := by
  unfold rotate
  simp only [Circle.coe_exp]
  exact (Complex.ofRealCLM.contDiff.mul contDiff_const).cexp

private theorem rotation_deriv (θ : ℝ) : HasDerivAt rotate (I*rotate θ) θ := by
  change HasDerivAt (fun s => (Circle.exp s : ℂ)) (I * (Circle.exp θ : ℂ)) θ
  simpa [Circle.coe_exp, mul_comm] using (((Complex.ofRealCLM.hasDerivAt (x := θ)).mul_const I).cexp)

private theorem rotation_lipschitz : LipschitzWith 1 rotate := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun x => (rotation_deriv x).differentiableAt)
  intro x
  rw [(rotation_deriv x).deriv]
  simp [rotate]

private def cart (σ : ℂ → ℝ) (u : Cartesian) : State :=
  let c := (cutoff (E := ℂ)) u.1 * (cutoff (E := ℂ × ℂ)) u.2 * Real.exp (-σ u.2.1)
  let d := u.1 * u.2.2
  (0,c • d,c * fderiv ℝ σ u.2.1 (I*d))

private theorem cart_smooth {σ : ℂ → ℝ} (hs : ContDiff ℝ ∞ σ) : ContDiff ℝ ∞ (cart σ) := by
  have grad := (hs.fderiv_right (m := ∞) (by simp)).comp (contDiff_fst.comp contDiff_snd :
    ContDiff ℝ ∞ (fun u : Cartesian => u.2.1))
  have coeff := (((cutoff (E := ℂ)).contDiff.comp contDiff_fst).mul
    ((cutoff (E := ℂ × ℂ)).contDiff.comp contDiff_snd)).mul
      ((hs.comp (contDiff_fst.comp contDiff_snd)).neg.exp)
  exact contDiff_const.prodMk ((coeff.smul (by fun_prop)).prodMk
    (coeff.mul (grad.clm_apply (by fun_prop))))

private theorem cart_compact (σ : ℂ → ℝ) : HasCompactSupport (cart σ) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Cartesian) 3)
  intro u hu
  by_contra! hn
  have h : 3 < ‖u‖ := lt_of_not_ge (mt mem_closedBall_zero_iff.mpr hn)
  have huge : 3 < ‖u.1‖ ∨ 3 < ‖u.2‖ := lt_max_iff.mp h
  rcases huge with hv | hw
  · exact hu (by simp [cart, (cutoff (E := ℂ)).zero_of_le_dist (x := u.1) (by simpa [cutoff] using hv.le)])
  · exact hu (by simp [cart, (cutoff (E := ℂ × ℂ)).zero_of_le_dist (x := u.2) (by simpa [cutoff] using hw.le)])

private def coords (p : State) : Cartesian := (p.1,p.2.1,rotate p.2.2)

def spray (σ : ℂ → ℝ) : State → State := cart σ ∘ coords

theorem spray_smooth {σ : ℂ → ℝ} (hs : ContDiff ℝ ∞ σ) : ContDiff ℝ ∞ (spray σ) :=
  (cart_smooth hs).comp (contDiff_fst.prodMk ((contDiff_fst.comp contDiff_snd).prodMk
    (rotation_smooth.comp (contDiff_snd.comp contDiff_snd))))

theorem spray_bounded {σ : ℂ → ℝ} (hs : ContDiff ℝ ∞ σ) :
    ∃ C : ℝ≥0, LipschitzWith C (spray σ) ∧ ∀ p, ‖spray σ p‖ ≤ C := by
  have cl := cart_smooth hs
  have supp := cart_compact σ
  obtain ⟨K, hK⟩ := cl.lipschitzWith_of_hasCompactSupport supp (by simp)
  have fst : LipschitzWith 1 (Prod.fst : State → ℂ) := LipschitzWith.prod_fst
  have snd : LipschitzWith 1 (Prod.snd : State → ℂ × ℝ) := LipschitzWith.prod_snd
  have second : LipschitzWith 1 (fun p : State => p.2.1) := by
    simpa using (LipschitzWith.prod_fst (α := ℂ) (β := ℝ)).comp snd
  have third : LipschitzWith 1 (fun p : State => p.2.2) := by
    simpa using (LipschitzWith.prod_snd (α := ℂ) (β := ℝ)).comp snd
  have l : LipschitzWith 1 coords := by
    simpa only [mul_one, max_self] using fst.prodMk (second.prodMk (rotation_lipschitz.comp third))
  obtain ⟨M, bound⟩ := supp.exists_bound_of_continuous cl.continuous
  refine ⟨max K M.toNNReal, ((by simpa using hK.comp l : LipschitzWith K (spray σ))).weaken
    (le_max_left _ _), fun p => ?_⟩
  exact (bound (coords p)).trans ((Real.le_coe_toNNReal M).trans (by exact_mod_cast le_max_right K M.toNNReal))

private theorem spray_first (σ : ℂ → ℝ) (p : State) : (spray σ p).1 = 0 := rfl

private theorem scale_law (σ : ℂ → ℝ) {v : ℂ} (hv : ‖v‖ ≤ 1) {c : ℝ} (hc : ‖c • v‖ ≤ 1)
    (z : ℂ) (δ : ℝ) : spray σ (c • v,z,δ) = c • spray σ (v,z,δ) := by
  have cut (u : ℂ) (h : ‖u‖ ≤ 1) : (cutoff (E := ℂ)) u = 1 :=
    (cutoff (E := ℂ)).one_of_mem_closedBall (mem_closedBall_zero_iff.mpr (by change ‖u‖ ≤ 2; linarith))
  simp only [spray, Function.comp_apply, coords, cart, cut _ hc, cut _ hv, one_mul,
    Prod.smul_mk, smul_zero, smul_mul_assoc, mul_smul_comm, map_smul, smul_eq_mul]
  congr 2
  · rw [smul_comm]
  · ring

private theorem timeScale_smooth : ContDiff ℝ ∞ (fun x : ℂ => Real.sqrt (1 + normSq x)) := by
  apply ContDiff.sqrt
  · change ContDiff ℝ ∞ (fun x : ℂ => 1 + (x.re*x.re+x.im*x.im))
    exact contDiff_const.add ((Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add
      (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff))
  · exact fun x => (add_pos_of_pos_of_nonneg zero_lt_one (normSq_nonneg x)).ne'

private def timeScale (x : ℂ) := Real.sqrt (1+normSq x)

private theorem timeScale_pos (x : ℂ) : 0 < timeScale x :=
  Real.sqrt_pos.mpr (add_pos_of_pos_of_nonneg zero_lt_one (normSq_nonneg _))

private theorem norm_le_timeScale (x : ℂ) : ‖x‖ ≤ timeScale x := by
  rw [timeScale, Real.le_sqrt (norm_nonneg _) (add_nonneg zero_le_one (normSq_nonneg x)), ← Complex.normSq_eq_norm_sq]
  linarith

private theorem fixed_parameter {σ : ℂ → ℝ} {Φ : State × ℝ → State}
    (zero : ∀ y, Φ (y,0) = y) (flow : ∀ y t, HasDerivAt (fun s => Φ (y,s)) (spray σ (Φ (y,t))) t)
    (y : State) (t : ℝ) : (Φ (y,t)).1 = y.1 := by
  have d (s : ℝ) : HasDerivAt (fun r => (Φ (y,r)).1) 0 s :=
    (ContinuousLinearMap.fst ℝ ℂ (ℂ × ℝ)).hasFDerivAt.comp_hasDerivAt s (flow y s)
  simpa [zero] using is_const_of_deriv_eq_zero (fun s => (d s).differentiableAt) (fun s => (d s).deriv) t 0

private theorem rescale_flow {σ : ℂ → ℝ} {Φ : State × ℝ → State} {K : ℝ≥0}
    (lip : LipschitzWith K (spray σ)) (zero : ∀ y, Φ (y,0) = y)
    (flow : ∀ y t, HasDerivAt (fun s => Φ (y,s)) (spray σ (Φ (y,t))) t)
    {v : ℂ} (hv : ‖v‖ ≤ 1) {c : ℝ} (hc : ‖c • v‖ ≤ 1) (a : ℂ) (t : ℝ) :
    (Φ ((c • v,a,0),t)).2 = (Φ ((v,a,0),c*t)).2 := by
  let y : State := (v,a,0)
  let g (s : ℝ) : State := (c • v, (Φ (y,c*s)).2)
  have d (s : ℝ) : HasDerivAt g (spray σ (g s)) s := by
    have line := (hasDerivAt_id s).const_mul c
    have ds := (flow y (c*s)).scomp s line
    have vel := (ContinuousLinearMap.snd ℝ ℂ (ℂ × ℝ)).hasFDerivAt.comp_hasDerivAt s ds
    have h := (hasDerivAt_const s (c • v)).prodMk vel
    have param : (Φ (y,c*s)).1 = v := fixed_parameter zero flow y _
    have eq : Φ (y,c*s) = (v, (Φ (y,c*s)).2) := Prod.ext param rfl
    convert h using 1
    rw [show g s = _ from rfl, scale_law σ hv hc, eq, mul_one]
    exact Prod.ext (smul_zero c) rfl
  have same := ODE_solution_unique_univ (v := fun _ => spray σ) (s := fun _ => univ)
    (fun _ => lip.lipschitzOnWith)
    (f := fun s => Φ ((c • v,a,0),s)) (fun s => ⟨flow _ s,trivial⟩)
    (g := g) (fun s => ⟨d s,trivial⟩) (t₀ := 0) (by simp [g,zero,y])
  exact (congrArg Prod.snd (congrFun same t) : (Φ ((c • v,a,0),t)).2 = (g t).2)

/-- The Cartesian endpoint and the parallel-frame rotation angle of each
ray are smooth through velocity zero. Their polar versions come from exactly
the same complete flow. -/
theorem joint_endpoint_and_angle {σ : ℂ → ℝ} (hs : ContDiff ℝ ∞ σ) :
    ∃ f : ℂ × ℂ → ℂ, ContDiff ℝ ∞ f ∧ ∀ a : ℂ, ∃ δ : ℂ → ℝ, ∃ F : (ℝ × ℝ) → Chart,
      ContDiff ℝ ∞ δ ∧ ContDiff ℝ ∞ F ∧ f (a,0) = a ∧
      (∀ α : ℝ, F (α,0) = (a,α,0)) ∧
      (∀ α t : ℝ, (F (α,t)).1 = f (a,t • (Circle.exp α : ℂ)) ∧
        (F (α,t)).2.1 = α + δ (t • (Circle.exp α : ℂ))) ∧
      ∀ q : ℝ × ℝ, ‖(F q).1‖ ≤ 1 →
        (fun u => fderiv ℝ F u (0,1)) =ᶠ[𝓝 q] X σ ∘ F := by
  obtain ⟨K,lip,bound⟩ := spray_bounded hs
  obtain ⟨Φ,sΦ,zero,D,_⟩ := GlobalGeodesicFlow.exists_flow (spray_smooth hs) lip bound
  let P₂ (q : ℂ × ℂ) := Φ (((timeScale q.2)⁻¹ • q.2,q.1,0),timeScale q.2)
  have scale_smooth : ContDiff ℝ ∞ timeScale := timeScale_smooth
  have sP₂ : ContDiff ℝ ∞ P₂ := sΦ.comp
    ((((scale_smooth.inv (fun x => (timeScale_pos x).ne')).comp contDiff_snd |>.smul contDiff_snd).prodMk
      (contDiff_fst.prodMk contDiff_const)).prodMk (scale_smooth.comp contDiff_snd))
  refine ⟨fun q => (P₂ q).2.1,contDiff_fst.comp (contDiff_snd.comp sP₂),fun a => ?_⟩
  let P (x : ℂ) := P₂ (a,x)
  let G (q : ℝ × ℝ) := Φ ((rotate q.1,a,0),q.2)
  let F (q : ℝ × ℝ) : Chart := ((G q).2.1,q.1 + (G q).2.2,0)
  have sp : ContDiff ℝ ∞ P := sP₂.comp (contDiff_const.prodMk contDiff_id)
  have sg : ContDiff ℝ ∞ G := sΦ.comp (((rotation_smooth.comp contDiff_fst).prodMk
    (contDiff_const (c := (a,(0:ℝ))))).prodMk contDiff_snd)
  have sf : ContDiff ℝ ∞ F := (contDiff_fst.comp (contDiff_snd.comp sg)).prodMk
    ((contDiff_fst.add (contDiff_snd.comp (contDiff_snd.comp sg))).prodMk contDiff_const)
  have pol (α t : ℝ) : (P (t • (rotate α))).2 = (G (α,t)).2 := by
    let x := t • rotate α
    let C := timeScale x
    have pos : 0 < C := timeScale_pos x
    have hv : ‖rotate α‖ = 1 := Circle.norm_coe _
    have normed : ‖C⁻¹ • x‖ ≤ 1 := by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr pos.le), ← div_eq_inv_mul]
      exact (div_le_one pos).mpr (norm_le_timeScale x)
    have h := rescale_flow lip zero D hv.le (c := C⁻¹ * t) (by simpa only [← smul_smul] using normed) a C
    simpa only [P, P₂, G, x, smul_smul, C, show C⁻¹ * t * C = t by field_simp] using h
  have central : (P 0).2 = (a,0) := by
    simpa [G,zero] using pol 0 0
  refine ⟨fun x => (P x).2.2,F,contDiff_snd.comp (contDiff_snd.comp sp), sf,congrArg Prod.fst central,?_,?_,?_⟩
  · intro α; simp [F,G,zero]
  · intro α t
    change (G (α,t)).2.1 = (P (t • rotate α)).2.1 ∧ α + (G (α,t)).2.2 = α + (P (t • rotate α)).2.2
    rw [pol]
    exact ⟨rfl,rfl⟩
  · intro q hq
    have near := ((contDiff_fst.comp sf).continuous.norm.continuousAt (x := q)).eventually_lt_const
      (show ‖(F q).1‖ < 2 by linarith)
    filter_upwards [near] with u hu
    let v := rotate u.1
    let p := G u
    have param : p.1 = v := fixed_parameter zero D (v,a,0) u.2
    have hv : ‖v‖ = 1 := Circle.norm_coe _
    have hw : ‖rotate p.2.2‖ = 1 := Circle.norm_coe _
    have hcut : (cutoff (E := ℂ) : ℂ → ℝ) p.1 = 1 :=
      (cutoff (E := ℂ)).one_of_mem_closedBall (mem_closedBall_zero_iff.mpr (by rw [param,hv]; norm_num [cutoff]))
    have hcut' : (cutoff (E := ℂ × ℂ) : (ℂ × ℂ) → ℝ) (p.2.1,rotate p.2.2) = 1 := by
      apply (cutoff (E := ℂ × ℂ)).one_of_mem_closedBall
      apply mem_closedBall_zero_iff.mpr
      exact max_le hu.le (hw.trans_le (by norm_num [cutoff]))
    have travel : p.1 * rotate p.2.2 = (Circle.exp (F u).2.1 : ℂ) := by
      rw [param]
      simp [v,rotate,F,p,Circle.exp_add]
    have vel := D (v,a,0) u.2
    have dz := (ContinuousLinearMap.fst ℝ ℂ ℝ).hasFDerivAt.comp_hasDerivAt u.2
      ((ContinuousLinearMap.snd ℝ ℂ (ℂ × ℝ)).hasFDerivAt.comp_hasDerivAt u.2 vel)
    have dδ := (ContinuousLinearMap.snd ℝ ℂ ℝ).hasFDerivAt.comp_hasDerivAt u.2
      ((ContinuousLinearMap.snd ℝ ℂ (ℂ × ℝ)).hasFDerivAt.comp_hasDerivAt u.2 vel)
    have sol := dz.prodMk ((dδ.const_add u.1).prodMk (hasDerivAt_const u.2 (0:ℝ)))
    have line : HasDerivAt (fun s : ℝ => (u.1,s)) (0,1) u.2 :=
      (hasDerivAt_const _ _).prodMk (hasDerivAt_id _)
    have fm := (sf.differentiable (by simp) u).hasFDerivAt.comp_hasDerivAt u.2 line
    rw [show fderiv ℝ F u (0,1) = ((spray σ p).2.1,(spray σ p).2.2,0) from fm.unique sol]
    change _ = X σ (F u)
    have chart := SimpleRadialVariation.chart_columns σ (F u)
    rw [chart.1]
    change ((spray σ p).2.1,(spray σ p).2.2,0) = _
    simp only [spray, Function.comp_apply, coords, cart, hcut, hcut', one_mul, travel, Complex.real_smul]
    congr 2
    congr 1
    change fderiv ℝ σ p.2.1 (I * (Circle.exp (F u).2.1 : ℂ)) = _
    rw [← SimpleRadialVariation.circle_normal]
    simp only [normal, map_add, map_smul, smul_eq_mul, Isothermal.angularDrift, Circle.coe_exp,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    ring

/-- Specialization of the joint Cartesian endpoint to one centre. -/
theorem endpoint_and_angle {σ : ℂ → ℝ} (hs : ContDiff ℝ ∞ σ) (a : ℂ) :
    ∃ f : ℂ → ℂ, ∃ δ : ℂ → ℝ, ∃ F : (ℝ × ℝ) → Chart,
      ContDiff ℝ ∞ f ∧ ContDiff ℝ ∞ δ ∧ ContDiff ℝ ∞ F ∧ f 0 = a ∧
      (∀ α : ℝ, F (α,0) = (a,α,0)) ∧
      (∀ α t : ℝ, (F (α,t)).1 = f (t • (Circle.exp α : ℂ)) ∧
        (F (α,t)).2.1 = α + δ (t • (Circle.exp α : ℂ))) ∧
      ∀ q : ℝ × ℝ, ‖(F q).1‖ ≤ 1 →
        (fun u => fderiv ℝ F u (0,1)) =ᶠ[𝓝 q] X σ ∘ F := by
  obtain ⟨f,sf,family⟩ := joint_endpoint_and_angle hs
  obtain ⟨δ,F,sd,sF,zero,ini,pol,ode⟩ := family a
  exact ⟨fun x => f (a,x),δ,F,sf.comp (contDiff_const.prodMk contDiff_id),sd,sF,zero,ini,pol,ode⟩

/-- On any simple chart every interior centre has an actual smooth geodesic
log on the whole open disk and a smooth ambient rotation angle in initial
Cartesian velocities. -/
theorem normal_coordinates {σ : ℂ → ℝ} (simple : SimpleDiskTarget.SimpleMetric σ) {a : ℂ}
    (ha : ‖a‖ < 1) :
    ∃ f : ℂ → ℂ, ∃ δ : ℂ → ℝ, ∃ F : (ℝ × ℝ) → Chart, ∃ L : ℂ → ℂ,
      ContDiff ℝ ∞ f ∧ ContDiff ℝ ∞ δ ∧ ContDiff ℝ ∞ F ∧ ContDiffOn ℝ ∞ L (ball (0 : ℂ) 1) ∧
      f 0 = a ∧ (∀ y ∈ ball (0 : ℂ) 1, L y ∈ SimpleRadialStar.retained f 1 ∧ f (L y) = y) ∧
      (∀ x ∈ SimpleRadialStar.retained f 1, f x ∈ ball (0 : ℂ) 1 → L (f x) = x) ∧
      (∀ α : ℝ, F (α,0) = (a,α,0)) ∧
      (∀ α t : ℝ, (F (α,t)).1 = f (t • (Circle.exp α : ℂ)) ∧
        (F (α,t)).2.1 = α + δ (t • (Circle.exp α : ℂ))) ∧
      ∀ q : ℝ × ℝ, ‖(F q).1‖ ≤ 1 → (fun u => fderiv ℝ F u (0,1)) =ᶠ[𝓝 q] X σ ∘ F := by
  obtain ⟨f,δ,F,sf,sd,sF,cent,ini,pol,ode⟩ := endpoint_and_angle simple.smooth a
  obtain ⟨L,sL,right,left⟩ := SimpleRadialVariation.smooth_log_of_geodesic_flow simple f F sf sF
    (cent ▸ ha) (fun α => by rw [ini,cent]) (fun α t => (pol α t).1) ode
  exact ⟨f,δ,F,L,sf,sd,sF,sL,cent,right,left,ini,pol,ode⟩

end TransportOkaGrauert.SimpleRadialSpray
