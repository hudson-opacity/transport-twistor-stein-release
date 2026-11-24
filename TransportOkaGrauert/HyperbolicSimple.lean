import TransportOkaGrauert.HyperbolicCR
import TransportOkaGrauert.HyperbolicDisk
import TransportOkaGrauert.HyperbolicRay
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Artanh

/-!
# Geometric simplicity for a Poincaré disk

A smooth cutoff applied outside a larger closed disk gives a conformal
factor smooth on the entire plane. Its curvature and boundary convexity
on the physical disk are unchanged. The Jacobi energy identity needs only
the one-sided derivatives required by the chart definition.
-/

noncomputable section
namespace TransportOkaGrauert.HyperbolicSimple
open Complex Set Metric SimpleDiskTarget HyperbolicCR Filter
open scoped ContDiff Topology ComplexConjugate

/-- The energy identity `(j j')' = (j')² − K j²` excludes two distinct
zeros whenever the Gaussian curvature is nonpositive along the segment. -/
theorem jacobi_nonpositive {a b : ℝ} (hab : a < b) {K j v : ℝ → ℝ}
    (d : ∀ t ∈ Icc a b, HasDerivWithinAt j (v t) (Icc a b) t ∧
      HasDerivWithinAt v (-(K t) * j t) (Icc a b) t)
    (hK : ∀ t ∈ Icc a b, K t ≤ 0) (ja : j a = 0) (jb : j b = 0) :
    ∀ t ∈ Icc a b, j t = 0 := by
  let P := fun t => j t * v t
  have dp (t : ℝ) (ht : t ∈ Icc a b) :
      HasDerivWithinAt P ((v t)^2 - K t * (j t)^2) (Icc a b) t := by
    convert (d t ht).1.mul (d t ht).2 using 1
    ring
  have mono : MonotoneOn P (Icc a b) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      (fun t ht => (dp t ht).continuousWithinAt)
      (fun t ht => (dp t (interior_subset ht)).mono interior_subset)
      (fun t ht => sub_nonneg.mpr (le_trans (mul_nonpos_of_nonpos_of_nonneg
        (hK t (interior_subset ht)) (sq_nonneg _)) (sq_nonneg _)))
  have vanished (t : ℝ) (ht : t ∈ Icc a b) : P t = 0 := by
    have lo := mono (left_mem_Icc.mpr hab.le) ht ht.1
    have hi := mono ht (right_mem_Icc.mpr hab.le) ht.2
    simpa [P, ja, jb] using (le_antisymm hi (by simpa [P, ja, jb] using lo) : P t = P b)
  have sqzero (t : ℝ) (ht : t ∈ Icc a b) :
      HasDerivWithinAt (fun t => (j t)^2) 0 (Icc a b) t := by
    convert (d t ht).1.pow 2 using 1
    have he := vanished t ht
    dsimp [P] at he
    rcases mul_eq_zero.mp he with hj | hv <;> simp [*]
  have const := constant_of_has_deriv_right_zero
    (fun t ht => (sqzero t ht).continuousWithinAt)
    (fun t ht => (sqzero t (mem_Icc_of_Ico ht)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht))
  intro t ht
  simpa [ja] using const t ht

private def margin (c : ℝ) := (1-c^2)/2
private def raw (c : ℝ) (z : ℂ) := 1-c^2*normSq z

/-- Outside the physical disk the logarithm is smoothly extended before
its singular circle. On the stated larger closed disk it is unchanged. -/
def globalFactor (c : ℝ) (z : ℂ) : ℝ :=
  let s := raw c z
  let m := margin c
  let χ := Real.smoothTransition (2*s/m-1);
  -Real.log (χ*s+(1-χ)*m)

def radius (c : ℝ) := (1+c)/(2*c)

private theorem margin_pos {c : ℝ} (hc : 0 < c) (hc' : c < 1) : 0 < margin c := by
  dsimp [margin]
  nlinarith [sq_nonneg c]

theorem one_lt_radius {c : ℝ} (hc : 0 < c) (hc' : c < 1) : 1 < radius c := by
  unfold radius
  exact (lt_div_iff₀ (by positivity)).mpr (by linarith)

private theorem smooth_raw (c : ℝ) : ContDiff ℝ ∞ (raw c) := by
  have h : normSq = fun z : ℂ => z.re^2+z.im^2 := by
    funext z; simp [normSq_apply, pow_two]
  unfold raw
  rw [h]
  exact contDiff_const.sub (contDiff_const.mul ((reCLM.contDiff.pow 2).add (imCLM.contDiff.pow 2)))

theorem smooth_globalFactor {c : ℝ} (hc : 0 < c) (hc' : c < 1) : ContDiff ℝ ∞ (globalFactor c) := by
  let m := margin c
  let χ := fun z => Real.smoothTransition (2*raw c z/m-1)
  have hm : 0 < m := margin_pos hc hc'
  have hχ : ContDiff ℝ ∞ χ := Real.smoothTransition.contDiff.comp
    (((contDiff_const.mul (smooth_raw c)).div_const m).sub contDiff_const)
  have pos (z : ℂ) : 0 < χ z * raw c z + (1-χ z)*m := by
    by_cases h : 2*raw c z/m-1 ≤ 0
    · simpa [χ, Real.smoothTransition.zero_of_nonpos h] using hm
    have hs : 0 < raw c z := by
      have h' : 1 < 2 * raw c z / m := by linarith
      have := (lt_div_iff₀ hm).mp h'
      linarith
    exact add_pos_of_pos_of_nonneg (mul_pos (Real.smoothTransition.pos_of_pos (lt_of_not_ge h)) hs)
      (mul_nonneg (sub_nonneg.mpr (Real.smoothTransition.le_one _)) hm.le)
  exact (((hχ.mul (smooth_raw c)).add ((contDiff_const.sub hχ).mul contDiff_const)).log (fun z => (pos z).ne')).neg

theorem factor_agrees {c : ℝ} (hc : 0 < c) (hc' : c < 1) {z : ℂ} (hz : ‖z‖ ≤ radius c) :
    globalFactor c =ᶠ[𝓝 z] factor c := by
  have hm := margin_pos hc hc'
  have hmul := (le_div_iff₀ (by positivity : 0 < 2*c)).mp hz
  have hsq : (c * ‖z‖)^2 ≤ ((1+c)/2)^2 :=
    pow_le_pow_left₀ (mul_nonneg hc.le (norm_nonneg z)) (by linarith) 2
  have hs : margin c < raw c z := by
    dsimp [raw, margin]
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [sq_pos_of_pos (sub_pos.mpr hc')]
  filter_upwards [(smooth_raw c).continuous.continuousAt.eventually_const_lt hs] with y hy
  have h : 1 ≤ 2*raw c y / margin c-1 := by
    have := (le_div_iff₀ hm).mpr (show 2*margin c ≤ 2*raw c y by linarith)
    linarith
  simp only [globalFactor, Real.smoothTransition.one_of_one_le h, one_mul, sub_self, zero_mul, add_zero]
  rfl

private theorem curvature_congr {σ τ : ℂ → ℝ} {z : ℂ} (eq : σ =ᶠ[𝓝 z] τ) :
    curvature σ z = curvature τ z := by
  have deriv (v : ℂ) :
      (fun y => fderiv ℝ σ y v) =ᶠ[𝓝 z] fun y => fderiv ℝ τ y v :=
    (eq.fderiv (𝕜 := ℝ)).mono fun y hy => DFunLike.congr_fun hy v
  simp [curvature, laplacian, eq.self_of_nhds, (deriv 1).fderiv_eq, (deriv I).fderiv_eq]

theorem curvature_globalFactor {c : ℝ} (hc : 0 < c) (hc' : c < 1) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    curvature (globalFactor c) z = -4*c^2 :=
  (curvature_congr (factor_agrees hc hc' (hz.trans (one_lt_radius hc hc').le))).trans
    (curvature_factor hc hc' hz)

theorem strict_boundary {c : ℝ} (hc : 0 < c) (hc' : c < 1) :
    ∀ z ∈ sphere (0 : ℂ) 1, 0 < 1 + fderiv ℝ (globalFactor c) z z := by
  intro z hz
  have hz' : ‖z‖ = 1 := by simpa [mem_sphere] using hz
  have hs := scale_pos hc hc' hz'.le
  rw [(factor_agrees hc hc' (hz'.le.trans (one_lt_radius hc hc').le)).fderiv_eq, factor_fderiv_apply hs.ne']
  have hsum : 0 ≤ z.re*z.re + z.im*z.im := add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)
  positivity

theorem no_conjugate {c : ℝ} (hc : 0 < c) (hc' : c < 1) {a b : ℝ} (hab : a < b)
    {z : ℝ → ℂ} (inside : ∀ t ∈ Icc a b, z t ∈ closedBall 0 1)
    {j v : ℝ → ℝ} (jac : jacobiOn (globalFactor c) z j v (Icc a b)) (ja : j a = 0) (jb : j b = 0) :
    ∀ t ∈ Icc a b, j t = 0 := by
  apply jacobi_nonpositive hab jac _ ja jb
  intro t ht
  rw [curvature_globalFactor hc hc' (mem_closedBall_zero_iff.mp (inside t ht))]
  nlinarith [sq_nonneg c]

/-- The first time a path crosses a strict intermediate level. The bound
holds throughout the intervening segment even if the path is nonmonotone. -/
private theorem first_level {f : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 1)) {R : ℝ}
    (h0 : f 0 < R) (h1 : R < f 1) :
    ∃ s ∈ Ioo (0 : ℝ) 1, f s = R ∧ ∀ t ∈ Icc 0 s, f t ≤ R := by
  let g := fun x => f (projIcc (0 : ℝ) 1 zero_le_one x)
  have hg : Continuous g := (continuousOn_iff_continuous_restrict.mp hf).comp continuous_projIcc
  have hg_eq {x : ℝ} (hx : x ∈ Icc 0 1) : g x = f x := by simp [g, projIcc_of_mem _ hx]
  let S := Icc (0 : ℝ) 1 ∩ {x | g x = R}
  have compactS : IsCompact S := isCompact_Icc.inter_right (isClosed_eq hg continuous_const)
  obtain ⟨s, hs, hfs⟩ := intermediate_value_Icc zero_le_one hf ⟨h0.le, h1.le⟩
  obtain ⟨m, hm, hmin⟩ := compactS.exists_isMinOn ⟨s, hs, (hg_eq hs).trans hfs⟩ continuous_id.continuousOn
  have fm : f m = R := (hg_eq hm.1).symm.trans hm.2
  have hm0 : 0 < m := lt_of_le_of_ne hm.1.1 (by rintro rfl; exact h0.ne fm)
  have hm1 : m < 1 := lt_of_le_of_ne hm.1.2 (by rintro rfl; exact h1.ne fm.symm)
  refine ⟨m, ⟨hm0,hm1⟩, fm, ?_⟩
  intro t ht
  by_contra! above
  obtain ⟨q, hq, fq⟩ := intermediate_value_Icc ht.1
    (hf.mono (Icc_subset_Icc_right (ht.2.trans hm.1.2))) ⟨h0.le, above.le⟩
  have hq01 : q ∈ Icc (0 : ℝ) 1 := ⟨hq.1, hq.2.trans (ht.2.trans hm.1.2)⟩
  have hmq : m ≤ q := isMinOn_iff.mp hmin q ⟨hq01, (hg_eq hq01).trans fq⟩
  have eq : t = m := le_antisymm ht.2 (hmq.trans hq.2)
  exact above.ne (eq ▸ fm.symm)

/-- Spatial parameter of a Poincaré geodesic, including the two ideal
boundary points when the diameter parameter is ±1. -/
private def spatial (c : ℝ) (z e : ℂ) (s : ℝ) : ℂ :=
  HyperbolicDisk.mob ((c:ℂ)*z) (e*(s:ℂ)) / (c:ℂ)

private theorem spatial_zero {c : ℝ} (hc : 0 < c) (z e : ℂ) : spatial c z e 0 = z := by
  simp [spatial, HyperbolicDisk.mob, hc.ne']

private theorem spatial_neg (c : ℝ) (z e : ℂ) (s : ℝ) : spatial c z e (-s) = spatial c z (-e) s := by
  simp [spatial]

private theorem stopped_diameter {c : ℝ} (hc : 0 < c) (hc' : c < 1) {z e : ℂ}
    (hz : ‖z‖ ≤ 1) (he : ‖e‖ = 1) :
    ∃ s ∈ Ioo (0 : ℝ) 1, ‖spatial c z e s‖ = radius c ∧
      ∀ r ∈ Icc 0 s, ‖spatial c z e r‖ ≤ radius c := by
  have ha : ‖(c:ℂ)*z‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
    exact (mul_le_of_le_one_right hc.le hz).trans_lt hc'
  have hnorm {r : ℝ} (hr : r ∈ Icc 0 1) : ‖e*(r:ℂ)‖ ≤ 1 := by
    rw [norm_mul, he, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr.1]
    exact hr.2
  apply first_level
  · apply ContinuousOn.norm
    have hlin : Continuous (fun r : ℝ => e * (r:ℂ)) := continuous_const.mul Complex.continuous_ofReal
    exact (((continuous_const.add hlin).continuousOn.div
      (continuous_const.add (continuous_const.mul hlin)).continuousOn
        (fun r hr => HyperbolicDisk.nonzero ha (hnorm hr))).div_const _)
  · rw [spatial_zero hc]
    exact hz.trans_lt (one_lt_radius hc hc')
  · rw [spatial, Complex.ofReal_one, mul_one, norm_div, HyperbolicDisk.norm_eq ha he,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
    unfold radius
    field_simp
    linarith

private theorem mono_tanh : Monotone Real.tanh := by
  intro x y hxy
  apply (Real.artanh_le_artanh_iff ⟨Real.neg_one_lt_tanh x, Real.tanh_lt_one x⟩
    ⟨Real.neg_one_lt_tanh y, Real.tanh_lt_one y⟩).mp
  simpa [Real.artanh_tanh] using hxy

/-- In both time directions the ray can be stopped strictly outside the
physical disk while staying inside the disk of agreement of the metrics. -/
theorem stopped_ray {c : ℝ} (hc : 0 < c) (hc' : c < 1) {z : ℂ} (hz : ‖z‖ ≤ 1) (θ : ℝ) :
    let path := fun t => HyperbolicDisk.mob ((c:ℂ)*z)
      ((Circle.exp θ : ℂ)*(Real.tanh (c*t):ℂ)) / (c:ℂ)
    ∃ a b : ℝ, a < 0 ∧ 0 < b ∧ 1 < ‖path a‖ ∧ 1 < ‖path b‖ ∧
      ∀ t ∈ Icc a b, ‖path t‖ ≤ radius c := by
  let e : ℂ := Circle.exp θ
  have he : ‖e‖ = 1 := Circle.norm_coe _
  obtain ⟨s, hs, hsend, hsbound⟩ := stopped_diameter hc hc' hz he
  obtain ⟨r, hr, hrend, hrbound⟩ := stopped_diameter hc hc' hz (show ‖-e‖ = 1 by simpa)
  let a := -Real.artanh r/c
  let b := Real.artanh s/c
  have ha : a < 0 := div_neg_of_neg_of_pos (neg_neg_of_pos (Real.artanh_pos hr)) hc
  have hb : 0 < b := div_pos (Real.artanh_pos hs) hc
  have fa : Real.tanh (c*a) = -r := by
    rw [show c*a = -Real.artanh r by dsimp [a]; field_simp, Real.tanh_neg, Real.tanh_artanh ⟨by linarith [hr.1], hr.2⟩]
  have fb : Real.tanh (c*b) = s := by
    rw [show c*b = Real.artanh s by dsimp [b]; field_simp, Real.tanh_artanh ⟨by linarith [hs.1], hs.2⟩]
  refine ⟨a,b,ha,hb,?_,?_,?_⟩
  · change 1 < ‖spatial c z e (Real.tanh (c*a))‖
    rw [fa, spatial_neg, hrend]
    exact one_lt_radius hc hc'
  · change 1 < ‖spatial c z e (Real.tanh (c*b))‖
    rw [fb, hsend]
    exact one_lt_radius hc hc'
  · intro t ht
    change ‖spatial c z e (Real.tanh (c*t))‖ ≤ radius c
    have hlow := mono_tanh (mul_le_mul_of_nonneg_left ht.1 hc.le)
    have hhigh := mono_tanh (mul_le_mul_of_nonneg_left ht.2 hc.le)
    rw [fa] at hlow
    rw [fb] at hhigh
    by_cases h : 0 ≤ Real.tanh (c*t)
    · exact hsbound _ ⟨h, hhigh⟩
    · rw [← neg_neg (Real.tanh (c*t)), spatial_neg]
      exact hrbound _ ⟨by linarith, by linarith⟩

/-- The physical Poincaré disk, represented by a conformal factor smooth
on the whole plane, satisfies the fixed-chart geometric simplicity definition. -/
theorem simple {c : ℝ} (hc : 0 < c) (hc' : c < 1) : SimpleMetric (globalFactor c) where
  smooth := smooth_globalFactor hc hc'
  strictConvex := strict_boundary hc hc'
  escapes := by
    intro z hz θ
    have hnorm := mem_closedBall_zero_iff.mp hz
    obtain ⟨a,b,ha,hb,hleft,hright,hinside⟩ := stopped_ray hc hc' hnorm θ
    refine ⟨a,b,HyperbolicRay.path c z θ,HyperbolicRay.angle c z θ,ha,hb,?_,HyperbolicRay.angle_zero c z θ,?_,hleft,hright⟩
    · simp [HyperbolicRay.path, HyperbolicDisk.mob, hc.ne']
    · intro t ht
      have eq := factor_agrees hc hc' (hinside t ht)
      have eq' : globalFactor c (HyperbolicRay.path c z θ t) = factor c (HyperbolicRay.path c z θ t) := eq.self_of_nhds
      have eqD : fderiv ℝ (globalFactor c) (HyperbolicRay.path c z θ t) = fderiv ℝ (factor c) (HyperbolicRay.path c z θ t) :=
        eq.fderiv_eq
      rw [eq']
      obtain ⟨hd,hθ⟩ := HyperbolicRay.equations hc hc' hnorm θ t
      refine ⟨hd.hasDerivWithinAt, ?_⟩
      simpa only [Isothermal.angularDrift, eqD] using hθ.hasDerivWithinAt (s := Icc a b)
  noConjugate := by
    intro a b hab z θ _ inside j v jac ja jb
    exact no_conjugate hc hc' hab inside jac ja jb

end TransportOkaGrauert.HyperbolicSimple
