import TransportOkaGrauert.GeodesicFlowExtension
import TransportOkaGrauert.SimpleRadialExit
import TransportOkaGrauert.CollarGluing

/-! # Convex exterior and absence of returning geodesics

The outward derivative of the conformal factor determines whether a tangent
geodesic has a strict local minimum of radius. A radial correction of the
extended conformal factor makes this sign positive everywhere outside the
disk while preserving the metric on a neighborhood of the closed disk. -/

noncomputable section
namespace TransportOkaGrauert.GeodesicNonreturn

open Complex SimpleDiskTarget SimpleRadialExit GeodesicFlowExtension CollarGluing Metric Set Filter
open scoped ContDiff Topology

/-- Radius on a geodesic joining two points of a disk cannot exceed the
disk radius when all the exterior radial level sets are strictly convex. -/
theorem stays_in_disk {σ z θ a b R} (ray : unitGeodesicOn σ z θ (Icc a b))
    (ha : ‖z a‖ ≤ R) (hb : ‖z b‖ ≤ R)
    (convex : ∀ p : ℂ, R < ‖p‖ → 0 < 1 + fderiv ℝ σ p p) :
    ∀ s ∈ Icc a b, ‖z s‖ ≤ R := by
  intro s hs
  by_contra! h
  let ρ := fun t => Complex.normSq (z t)
  have dρ : ContinuousOn ρ (Icc a b) := Complex.continuous_normSq.comp_continuousOn
    fun t ht => (ray t ht).1.continuousWithinAt
  obtain ⟨T,hT,maxT⟩ := isCompact_Icc.exists_isMaxOn ⟨s,hs⟩ dρ
  have dom := isMaxOn_iff.mp maxT s hs
  change Complex.normSq (z s) ≤ Complex.normSq (z T) at dom
  simp only [Complex.normSq_eq_norm_sq] at dom
  have hR : R < ‖z T‖ := by nlinarith [norm_nonneg (z s), norm_nonneg (z T), norm_nonneg (z a)]
  have lT : a < T := lt_of_le_of_ne hT.1 (fun e => (not_lt_of_ge ha) (e ▸ hR))
  have rT : T < b := lt_of_le_of_ne hT.2 (fun e => (not_lt_of_ge hb) (e ▸ hR))
  have nearT := Icc_mem_nhds lT rT
  have zer := (maxT.isLocalMax nearT).hasDerivAt_eq_zero (radiusSq_deriv ray nearT)
  let n := fun s => normal (z s) (Circle.exp (θ s))
  have tan : n T = 0 := (mul_eq_zero.mp zer).resolve_left (by positivity)
  have dn := normal_deriv_at_tangent ray nearT tan
  have slopePos := (hasDerivAt_iff_tendsto_slope_left_right.mp dn).2.eventually
    (Ioi_mem_nhds (mul_pos (Real.exp_pos _) (convex _ hR)))
  have right : ∀ᶠ u in 𝓝[>] T, 0 < n u := by
    filter_upwards [slopePos, self_mem_nhdsWithin] with u hu hut
    change T < u at hut
    change 0 < slope n T u at hu
    rw [slope_def_field, tan, sub_zero] at hu
    exact (div_pos_iff_of_pos_right (sub_pos.mpr hut)).mp hu
  obtain ⟨v,hv,hsub⟩ := (mem_nhdsGT_iff_exists_mem_Ioc_Ioo_subset rT).mp right
  have sub : Icc T v ⊆ Icc a b := Icc_subset_Icc hT.1 hv.2
  obtain ⟨u,hu,hu'⟩ := exists_hasDerivAt_eq_slope ρ _ hv.1 (dρ.mono sub) (fun u hu =>
    radiusSq_deriv ray (Icc_mem_nhds (lT.trans hu.1) (hu.2.trans_le hv.2)))
  have hle : ρ v ≤ ρ T := isMaxOn_iff.mp maxT v (sub ⟨hv.1.le,le_rfl⟩)
  have hpos := mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) (Real.exp_pos (-σ (z u)))) (hsub hu)
  exact (not_lt_of_ge (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hle) (sub_nonneg.mpr hv.1.le)))
    (hu' ▸ hpos)

private def outward (σ : ℂ → ℝ) (z : ℂ) := 1 + fderiv ℝ σ z z

private theorem outward_continuous {σ : ℂ → ℝ} (hs : ContDiff ℝ ∞ σ) : Continuous (outward σ) :=
  continuous_const.add ((hs.continuous_fderiv (by simp)).clm_apply continuous_id)

private theorem strict_annulus {σ : ℂ → ℝ} (simple : SimpleMetric σ) :
    ∃ d > 0, d ≤ 1/4 ∧ ∀ z : ℂ, 1 ≤ Complex.normSq z → Complex.normSq z ≤ 1+2*d →
      0 < outward (extendedFactor σ) z := by
  let A := outward (extendedFactor σ)
  have dA := outward_continuous (factor_smooth simple.smooth)
  have circle (z : ℂ) (hz : ‖z‖ = 1) : 0 < A z := by
    have eq := factor_eq (σ := σ) (show ‖z‖ < 2 by linarith)
    simpa [A,outward,eq.fderiv_eq] using simple.strictConvex z (by simpa using hz)
  let K := closedBall (0 : ℂ) 2 ∩ {z : ℂ | 1 ≤ Complex.normSq z} ∩ {z : ℂ | A z ≤ 0}
  have compact : IsCompact K := ((isCompact_closedBall (0 : ℂ) 2).inter_right
    (isClosed_le continuous_const Complex.continuous_normSq)).inter_right (isClosed_le dA continuous_const)
  have mem (z : ℂ) (h : 1 ≤ Complex.normSq z) (h' : Complex.normSq z ≤ 2) (hA : A z ≤ 0) : z ∈ K := by
    refine ⟨⟨?_,h⟩,hA⟩
    simp only [mem_closedBall, dist_zero_right]
    rw [Complex.normSq_eq_norm_sq] at h'
    nlinarith [norm_nonneg z]
  by_cases hK : K.Nonempty
  · obtain ⟨m,hm,hmin⟩ := compact.exists_isMinOn hK Complex.continuous_normSq.continuousOn
    have hmpos : 1 < Complex.normSq m := (lt_of_le_of_ne hm.1.2 fun eq => by
      have n : ‖m‖ = 1 := by rw [Complex.normSq_eq_norm_sq] at eq; nlinarith [norm_nonneg m]
      exact (not_lt_of_ge hm.2) (circle _ n))
    let d := min (1/4 : ℝ) ((Complex.normSq m-1)/4)
    refine ⟨d, lt_min (by norm_num) (by linarith), min_le_left .., ?_⟩
    intro z lo hi
    by_contra! ha
    have hd : d ≤ 1/4 := min_le_left .. 
    have hd' : d ≤ (Complex.normSq m-1)/4 := min_le_right ..
    have le := isMinOn_iff.mp hmin z (mem z lo (by linarith) ha)
    linarith
  · refine ⟨1/4,by norm_num,le_rfl,?_⟩
    intro z lo hi
    by_contra! ha
    exact hK ⟨z,mem z lo (by linarith) ha⟩

private def profile (d q : ℝ) : ℝ :=
  d * (ramp ((q-(1+d))/d) - ramp ((q-10)/d))

private theorem profile_smooth (d : ℝ) : ContDiff ℝ ∞ (profile d) :=
  contDiff_const.mul ((ramp_smooth.comp ((contDiff_id.sub contDiff_const).div_const _)).sub
    (ramp_smooth.comp ((contDiff_id.sub contDiff_const).div_const _)))

private def rate (d q : ℝ) : ℝ :=
  Real.smoothTransition ((q-(1+d))/d) - Real.smoothTransition ((q-10)/d)

private theorem profile_deriv {d : ℝ} (hd : 0 < d) (q : ℝ) :
    HasDerivAt (profile d) (rate d q) q := by
  have df (c : ℝ) := (ramp_deriv ((q-c)/d)).comp q (((hasDerivAt_id q).sub_const c).div_const d)
  have a := ((df (1+d)).sub (df 10)).const_mul d
  convert a using 1
  dsimp [rate]
  field_simp

private theorem smooth_sq : ContDiff ℝ ∞ Complex.normSq := by
  have eq : Complex.normSq = fun z : ℂ => z.re^2 + z.im^2 := by funext z; simp [Complex.normSq_apply, pow_two]
  rw [eq]
  exact (reCLM.contDiff.pow 2).add (imCLM.contDiff.pow 2)

private theorem radial_sq (z : ℂ) : fderiv ℝ Complex.normSq z z = 2 * Complex.normSq z := by
  have d := (reCLM.hasFDerivAt (x := z)).mul reCLM.hasFDerivAt |>.add
    (imCLM.hasFDerivAt.mul imCLM.hasFDerivAt)
  change HasFDerivAt Complex.normSq _ z at d
  rw [d.fderiv]
  simp [Complex.normSq_apply]
  ring

private def correction (σ : ℂ → ℝ) (d C : ℝ) (z : ℂ) : ℝ :=
  extendedFactor σ z + C * profile d (Complex.normSq z)

private theorem correction_outward {σ : ℂ → ℝ} (hs : ContDiff ℝ ∞ σ) {d : ℝ} (hd : 0 < d)
    (C : ℝ) (z : ℂ) : outward (correction σ d C) z =
      outward (extendedFactor σ) z + C * (rate d (Complex.normSq z) * (2 * Complex.normSq z)) := by
  have de := ((factor_smooth hs).differentiable (by simp) z).hasFDerivAt
  have dr := (profile_deriv hd _).comp_hasFDerivAt z ((smooth_sq.differentiable (by simp) z).hasFDerivAt)
  have D := de.add (dr.const_mul C)
  change HasFDerivAt (correction σ d C) _ z at D
  simp [outward,D.fderiv,radial_sq,add_assoc]

/-- A smooth factor agreeing with the input on a neighborhood of the closed
disk, constant near infinity, and with strictly convex exterior radial levels. -/
theorem exists_convex_extension {σ : ℂ → ℝ} (simple : SimpleMetric σ) :
    ∃ τ : ℂ → ℝ, ContDiff ℝ ∞ τ ∧
      (∃ e > (0:ℝ), ∀ z : ℂ, Complex.normSq z < 1+e → τ z = σ z) ∧
      (∃ c : ℝ, ∀ z : ℂ, 4 < ‖z‖ → τ z = c) ∧
      ∀ z : ℂ, 1 ≤ ‖z‖ → 0 < 1 + fderiv ℝ τ z z := by
  obtain ⟨d,hd,hd',collar⟩ := strict_annulus simple
  let A := outward (extendedFactor σ)
  have dA := outward_continuous (factor_smooth simple.smooth)
  obtain ⟨m,hm,hmax⟩ := (isCompact_closedBall (0 : ℂ) 3).exists_isMaxOn
    (show (closedBall (0 : ℂ) 3).Nonempty by exact ⟨0,by simp⟩) dA.abs.continuousOn
  let C := |A m| + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨correction σ d C, (factor_smooth simple.smooth).add
    (contDiff_const.mul ((profile_smooth d).comp smooth_sq)), ⟨d,hd,?_⟩, ?_, ?_⟩
  · intro z hz
    have hz' : ‖z‖ < 2 := by rw [Complex.normSq_eq_norm_sq] at hz; nlinarith [norm_nonneg z]
    have left : (Complex.normSq z-(1+d))/d ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hd.le
    have right : (Complex.normSq z-10)/d ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hd.le
    simp [correction,profile,ramp_inactive left,ramp_inactive right,(factor_eq hz').eq_of_nhds]
  · refine ⟨C * (9-d),?_⟩
    intro z hz
    have big : 16 < Complex.normSq z := by rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg z]
    have left : 1 ≤ (Complex.normSq z-(1+d))/d := (le_div_iff₀ hd).mpr (by linarith)
    have right : 1 ≤ (Complex.normSq z-10)/d := (le_div_iff₀ hd).mpr (by linarith)
    simp [correction,(factor_flat (lt_trans (by norm_num) hz)).eq_of_nhds,profile,
      ramp_active left,ramp_active right]
    field_simp
    ring_nf
    simp
  · intro z hnorm
    change 0 < outward (correction σ d C) z
    rw [correction_outward simple.smooth hd]
    let q := Complex.normSq z
    have hq : 1 ≤ q := by dsimp [q]; rw [Complex.normSq_eq_norm_sq]; nlinarith
    have pos : 0 ≤ rate d q := by
      apply sub_nonneg.mpr
      exact Real.smoothTransition.monotone (div_le_div_of_nonneg_right (by linarith) hd.le)
    change 0 < A z + C * (rate d q * (2*q))
    by_cases near : q ≤ 1+2*d
    · exact add_pos_of_pos_of_nonneg (collar z hq near) (by positivity)
    by_cases far : 3 < ‖z‖
    · have flat := factor_flat (σ := σ) far
      have hA : A z = 1 := by simp [A,outward,flat.fderiv_eq]
      rw [hA]
      positivity
    have h9 : q ≤ 9 := by dsimp [q]; rw [Complex.normSq_eq_norm_sq]; nlinarith [le_of_not_gt far]
    have one : rate d q = 1 := by
      have left : 1 ≤ (q-(1+d))/d := (le_div_iff₀ hd).mpr (by linarith [lt_of_not_ge near])
      have right : (q-10)/d ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hd.le
      simp [rate,Real.smoothTransition.one_of_one_le left,Real.smoothTransition.zero_of_nonpos right]
    have bound : -A z ≤ |A m| := (neg_le_abs _).trans (isMaxOn_iff.mp hmax z (by simpa using le_of_not_gt far))
    rw [one,one_mul]
    dsimp [C]
    nlinarith [mul_nonneg (abs_nonneg (A m)) (sub_nonneg.mpr hq)]

end TransportOkaGrauert.GeodesicNonreturn
