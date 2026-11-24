import TransportOkaGrauert.JacobiEnlargement
import TransportOkaGrauert.SimpleRadialVariation

/-! # A simple enlargement of every simple conformal disk

Coordinates on the enlarged disk are divided by its radius. The conformal
factor consequently gains the constant logarithm of the radius; arclength
and the scalar Jacobi equation retain their original normalization.
-/

noncomputable section
namespace TransportOkaGrauert.SimpleEnlargement

open SimpleDiskTarget Complex Metric Set Filter ChartJacobi JacobiEnlargement GeodesicFlowExtension
open scoped ContDiff Topology

def rescale (τ : ℂ → ℝ) (R : ℝ) (z : ℂ) : ℝ := τ (R • z) + Real.log R

private def dilation (R : ℝ) : ℂ →L[ℝ] ℂ := R • ContinuousLinearMap.id ℝ ℂ

theorem rescale_smooth {τ : ℂ → ℝ} (hτ : ContDiff ℝ ∞ τ) (R : ℝ) : ContDiff ℝ ∞ (rescale τ R) :=
  (hτ.comp (dilation R).contDiff).add contDiff_const

theorem rescale_fderiv {τ : ℂ → ℝ} (hτ : ContDiff ℝ ∞ τ) (R : ℝ) (z v : ℂ) :
    fderiv ℝ (rescale τ R) z v = R * fderiv ℝ τ (R • z) v := by
  have d := (((hτ.differentiable (by simp) (R • z)).hasFDerivAt).comp z (dilation R).hasFDerivAt).add_const (Real.log R)
  change HasFDerivAt (rescale τ R) _ z at d
  rw [d.fderiv]
  simp [dilation]

theorem rescale_curvature {τ : ℂ → ℝ} (hτ : ContDiff ℝ ∞ τ) {R : ℝ} (hR : 0 < R) (z : ℂ) :
    curvature (rescale τ R) z = curvature τ (R • z) := by
  have second (v : ℂ) :
      fderiv ℝ (fun x => fderiv ℝ (rescale τ R) x v) z v =
      R^2 * fderiv ℝ (fun x => fderiv ℝ τ x v) (R • z) v := by
    have dh := ((hτ.fderiv_right (m := ∞) (by simp)).differentiable (by simp) (R • z)).hasFDerivAt.clm_apply
      (hasFDerivAt_const v (R • z))
    have ds := (dh.comp z (dilation R).hasFDerivAt).const_mul R
    simp_rw [rescale_fderiv hτ]
    change HasFDerivAt (fun x => R * fderiv ℝ τ (R • x) v) _ z at ds
    rw [ds.fderiv,dh.fderiv]
    simp [dilation,pow_two,mul_assoc]
  have he : Real.exp (-2 * rescale τ R z) = Real.exp (-2*τ (R • z)) / R^2 := by
    rw [rescale, mul_add,Real.exp_add,show -2 * Real.log R = -(2*Real.log R) by ring,
      Real.exp_neg,show Real.exp (2*Real.log R) = R^2 by rw [two_mul, Real.exp_add,Real.exp_log hR,pow_two]]
    rfl
  simp only [curvature,laplacian,second,he]
  field_simp

private theorem exp_rescale {τ : ℂ → ℝ} {R : ℝ} (hR : 0 < R) (z : ℂ) :
    Real.exp (-(rescale τ R z)) = Real.exp (-τ (R • z)) / R := by
  simp [rescale,Real.exp_add,Real.exp_neg,Real.exp_log hR,div_eq_mul_inv,mul_comm]

private theorem drift_rescale {τ : ℂ → ℝ} (hτ : ContDiff ℝ ∞ τ) (R : ℝ) (z : ℂ) (w : Circle) :
    Isothermal.angularDrift (rescale τ R) z w = R * Isothermal.angularDrift τ (R • z) w := by
  simp [Isothermal.angularDrift,rescale_fderiv hτ,mul_sub,mul_assoc]

theorem rescale_ray {τ : ℂ → ℝ} (hτ : ContDiff ℝ ∞ τ) {R : ℝ} (hR : 0 < R) {z θ s}
    (h : unitGeodesicOn (rescale τ R) z θ s) : unitGeodesicOn τ (fun t => R • z t) θ s := by
  intro t ht
  obtain ⟨dz,dθ⟩ := h t ht
  constructor
  · convert dz.const_smul R using 1
    rw [exp_rescale hR,Complex.real_smul,Complex.ofReal_div]
    field_simp [show (R:ℂ) ≠ 0 by exact_mod_cast hR.ne']
  · convert dθ using 1
    rw [exp_rescale hR,drift_rescale hτ]
    field_simp

theorem unscale_ray {τ : ℂ → ℝ} (hτ : ContDiff ℝ ∞ τ) {R : ℝ} (hR : 0 < R) {z θ s}
    (h : unitGeodesicOn τ z θ s) : unitGeodesicOn (rescale τ R) (fun t => R⁻¹ • z t) θ s := by
  intro t ht
  obtain ⟨dz,dθ⟩ := h t ht
  constructor
  · convert dz.const_smul R⁻¹ using 1
    simp [exp_rescale hR,hR.ne',Complex.real_smul,div_eq_inv_mul,mul_assoc]
  · convert dθ using 1
    rw [exp_rescale hR,drift_rescale hτ,smul_smul,mul_inv_cancel₀ hR.ne',one_smul]
    field_simp

variable {σ : ℂ → ℝ} (F : JacobiEnlargement.Flow σ)

private theorem ray_in_flow {z θ a b} (ray : unitGeodesicOn F.factor z θ (Icc a b)) :
    EqOn (fun t => (z t,θ t)) (fun t => F.val ((z a,θ a),t-a)) (Icc a b) := by
  apply ScalarGeneralUnrestricted.endpoint_unique (X := PathContinuation.chartVector F.factor)
    (contDiff_iff_contDiffAt.mpr (fun p => ChartRegularity.chartVector_contDiffAt p F.smoothFactor.contDiffAt))
  · intro t ht
    exact (ray t ht).1.prodMk (ray t ht).2
  · intro t _
    simpa only [Function.comp_def,sub_self,one_smul] using
      ((F.ode (z a,θ a) (t-a)).scomp t ((hasDerivAt_id t).sub_const a)).hasDerivWithinAt
  · exact Or.inl (by simp [F.initial])

private def matrix (k : ℝ) : (ℝ × ℝ) →L[ℝ] ℝ × ℝ :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).prod (-k • ContinuousLinearMap.fst ℝ ℝ ℝ)

private theorem jacobi_eq {T t : ℝ} (hT : 0 ≤ T) (ht : t ∈ Icc 0 T) {p : State}
    {j dj : ℝ → ℝ} (hj : jacobiOn F.factor (F.base p) j dj (Icc 0 t)) (hzero : j 0 = 0) :
    ∀ s ∈ Icc 0 t, j s = dj 0 * field hT (F.curvaturePath T p) s := by
  let k := F.curvaturePath T p
  let A := fun s => matrix (curvature F.factor (F.base p s))
  have eqM : matrix = fun k => (ContinuousLinearMap.snd ℝ ℝ ℝ).prod (0 : (ℝ × ℝ) →L[ℝ] ℝ) +
      (-k) • (0 : (ℝ × ℝ) →L[ℝ] ℝ).prod (ContinuousLinearMap.fst ℝ ℝ ℝ) := by
    funext k
    apply ContinuousLinearMap.ext
    intro w
    simp [matrix]
  have hcm : Continuous matrix := eqM ▸ continuous_const.add (continuous_id.neg.smul continuous_const)
  have ca : Continuous A := hcm.comp ((curvature_contDiff F.smoothFactor).continuous.comp
    (continuous_fst.comp (F.smooth.continuous.comp (continuous_const.prodMk continuous_id))))
  have eq := SimpleRadialVariation.linear_unique ca.continuousOn
    (u := fun s => (j s,dj s)) (v := fun s => dj 0 • (field hT k s,speed hT k s))
    (fun s hs => (hj s hs).1.prodMk (hj s hs).2)
    (fun s hs => by
      have sub : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc_right ht.2
      obtain ⟨jj,jd⟩ := solves hT k s (sub hs)
      have der := ((jj.mono sub).prodMk (jd.mono sub)).const_smul (dj 0)
      convert der using 1
      change A s (dj 0 • (field hT k s,speed hT k s)) = _
      rw [map_smul]
      rfl)
    (by simp [hzero,(initial_values hT k).1,(initial_values hT k).2])
  exact fun s hs => congrArg Prod.fst (eq hs)

private theorem no_conjugates {R T c : ℝ} (hT : 0 < T) (hc : 0 < c)
    (escape : ∀ p : State, ‖p.1‖ ≤ R → R < ‖F.base p T‖)
    (margin : ∀ p : State, ‖p.1‖ ≤ R → ∀ t ∈ Icc 0 T, ‖F.base p t‖ ≤ R →
      c ≤ F.quotient hT.le (p,t)) {a b} (hab : a < b) {z θ}
    (ray : unitGeodesicOn F.factor z θ (Icc a b)) (disk : ∀ t ∈ Icc a b, ‖z t‖ ≤ R)
    {j dj} (jc : jacobiOn F.factor z j dj (Icc a b)) (ja : j a = 0) (jb : j b = 0) :
    ∀ t ∈ Icc a b, j t = 0 := by
  let p := (z a,θ a)
  have da : ‖p.1‖ ≤ R := disk a (left_mem_Icc.mpr hab.le)
  have eq (s : ℝ) (hs : s ∈ Icc 0 (b-a)) : z (a+s) = F.base p s := by
    have e := congrArg Prod.fst (ray_in_flow F ray (x := a+s) (by constructor <;> linarith [hs.1,hs.2]))
    simpa [p, JacobiEnlargement.Flow.base] using e
  have tb : b-a ≤ T := by
    by_contra! h
    have e := eq T ⟨hT.le,h.le⟩
    have d := disk (a+T) (by constructor <;> linarith)
    exact (not_lt_of_ge (e ▸ d)) (escape p da)
  have map : MapsTo (fun s => a+s) (Icc 0 (b-a)) (Icc a b) := fun s hs =>
    ⟨by linarith [hs.1],by linarith [hs.2]⟩
  have jray : jacobiOn F.factor (F.base p) (fun s => j (a+s)) (fun s => dj (a+s)) (Icc 0 (b-a)) := by
    intro s hs
    have ds := ((hasDerivAt_id s).const_add a).hasDerivWithinAt (s := Icc 0 (b-a))
    obtain ⟨d₁,d₂⟩ := jc (a+s) (map hs)
    exact ⟨by simpa only [Function.comp_def,mul_one] using d₁.comp s ds map,
      by simpa only [Function.comp_def,mul_one,eq s hs] using d₂.comp s ds map⟩
  have h := jacobi_eq F hT.le ⟨sub_nonneg.mpr hab.le,tb⟩ jray (by simpa using ja)
  have right := right_mem_Icc.mpr (sub_nonneg.mpr hab.le)
  have endEq : z b = F.base p (b-a) := by simpa using eq (b-a) right
  have pos := hc.trans_le (margin p da (b-a) ⟨sub_nonneg.mpr hab.le,tb⟩
    (endEq ▸ disk b (right_mem_Icc.mpr hab.le)))
  have posJ : 0 < field hT.le (F.curvaturePath T p) (b-a) := by
    rw [F.field_eq_mul_quotient hT.le p ⟨sub_nonneg.mpr hab.le,tb⟩]
    exact mul_pos (sub_pos.mpr hab) pos
  have last := h (b-a) right
  have slope : dj a = 0 := (mul_eq_zero.mp (by simpa [jb] using last.symm :
    dj a * field hT.le (F.curvaturePath T p) (b-a) = 0)).resolve_right posJ.ne'
  intro s hs
  simpa [slope] using h (s-a) ⟨sub_nonneg.mpr hs.1,sub_le_sub_right hs.2 a⟩

/-- A simple radius for the same complete convex extension used to solve the geodesic ODE. -/
theorem simple_radius (simple : SimpleMetric σ) : ∃ R > 1, SimpleMetric (rescale F.factor R) := by
  obtain ⟨T,hT,R₀,h₀,_,out⟩ := F.uniform_escape simple
  obtain ⟨R₁,h₁,_,c,hc,pos⟩ := F.jacobi_margin hT.le simple
  let R := min R₀ R₁
  have hR : 1 < R := lt_min h₀ h₁
  have hr : 0 < R := zero_lt_one.trans hR
  have hR₀ : R ≤ R₀ := min_le_left ..
  have hR₁ : R ≤ R₁ := min_le_right ..
  have esc (p : State) (hp : ‖p.1‖ ≤ R) : R < ‖F.base p T‖ := hR₀.trans_lt (out p (hp.trans hR₀))
  refine ⟨R,hR,?_⟩
  constructor
  · exact rescale_smooth F.smoothFactor R
  · intro z hz
    have hn : ‖z‖ = 1 := by simpa using hz
    have norm : ‖R • z‖ = R := by simp [Real.norm_of_nonneg hr.le,hn]
    simpa only [rescale_fderiv F.smoothFactor, map_smul, smul_eq_mul] using F.convex (R • z) (by rw [norm]; exact hR.le)
  · intro z hz θ
    let p : State := (R • z,θ)
    have hp : ‖p.1‖ ≤ R := by
      simpa [p,norm_smul,Real.norm_of_nonneg hr.le] using
        mul_le_of_le_one_right hr.le (mem_closedBall_zero_iff.mp hz)
    have back : R < ‖F.base p (-T)‖ := by
      by_contra! lock
      have e := esc (F.val (p,-T)) lock
      simp [JacobiEnlargement.Flow.base,F.group,F.initial,not_lt_of_ge hp] at e
    have outer (v : ℂ) (hv : R < ‖v‖) : 1 < ‖R⁻¹ • v‖ := by
      rw [norm_smul,Real.norm_of_nonneg (inv_pos.mpr hr).le,← div_eq_inv_mul]
      exact (one_lt_div hr).mpr hv
    exact ⟨-T,T,fun s => R⁻¹ • F.base p s, F.angle p,neg_neg_of_pos hT,hT,
      by simp [JacobiEnlargement.Flow.base,F.initial,p,hr.ne'],
      by simp [JacobiEnlargement.Flow.angle,F.initial,p],
      unscale_ray F.smoothFactor hr (F.geo p _),outer _ back,outer _ (esc p hp)⟩
  · intro a b hab z θ ray disk j dj jc ja jb
    have scaled := rescale_ray F.smoothFactor hr ray
    have enlarged (s : ℝ) (hs : s ∈ Icc a b) : ‖R • z s‖ ≤ R := by
      simpa [norm_smul,Real.norm_of_nonneg hr.le] using
        mul_le_of_le_one_right hr.le (mem_closedBall_zero_iff.mp (disk s hs))
    have same : jacobiOn F.factor (fun s => R • z s) j dj (Icc a b) := by
      intro s hs
      simpa only [rescale_curvature F.smoothFactor hr] using jc s hs
    exact no_conjugates F hT hc esc (fun p hp t ht he => pos p (hp.trans hR₁) t ht (he.trans hR₁))
      hab scaled enlarged same ja jb

/-- Rescaling a slightly larger disk yields a simple metric on the standard
unit disk, with a smooth metric extension that agrees with the input on an
open neighborhood of the entire original disk, including boundary centres. -/
theorem exists_simple_enlargement {σ : ℂ → ℝ} (simple : SimpleMetric σ) :
    ∃ R > 1, ∃ τ : ℂ → ℝ, SimpleMetric (rescale τ R) ∧ ContDiff ℝ ∞ τ ∧
      ∃ e > (0:ℝ), ∀ z : ℂ, normSq z < 1+e → τ z = σ z := by
  obtain ⟨F⟩ := JacobiEnlargement.exists_flow simple
  obtain ⟨R,hR,sl⟩ := simple_radius F simple
  exact ⟨R,hR,F.factor,sl,F.smoothFactor,F.agrees⟩

end TransportOkaGrauert.SimpleEnlargement
