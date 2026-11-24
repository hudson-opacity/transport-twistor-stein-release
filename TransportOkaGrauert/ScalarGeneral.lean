import TransportOkaGrauert.ScalarGeneralCauchy
import TransportOkaGrauert.PencilLifts
import Mathlib.Analysis.Complex.RemovableSingularity

/-! The single negative mode in the pencil solver can be removed on every
conformal disk. A Cauchy–Green base primitive cancels it. Radial division of
the remaining disk function preserves joint ambient smoothness. -/
noncomputable section
namespace TransportOkaGrauert.ScalarGeneral
open Complex Metric Set MeasureTheory ChartStein ChartCorrespondence PencilLifts ScalarGeneralCauchy
open scoped ContDiff ComplexConjugate

private def verticalSlope (f : DiskFunction) (p : E) := fderiv ℝ f.val p (0,1)
private theorem smooth_slope (f : DiskFunction) : ContDiff ℝ ∞ (verticalSlope f) :=
  (f.smooth.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

private def quotient (f : DiskFunction) (p : E) : ℂ :=
  ∫ t in (0:ℝ)..1, verticalSlope f (p.1, (t:ℂ)*p.2)

private theorem smooth_quotient (f : DiskFunction) : ContDiff ℝ ∞ (quotient f) := by
  apply integral_smooth (g := fun p : E × ℝ => verticalSlope f (p.1.1, (p.2:ℂ)*p.1.2)) _ one_pos
  exact (smooth_slope f).comp ((contDiff_fst.comp contDiff_fst).prodMk
    ((Complex.ofRealCLM.contDiff.comp contDiff_snd).mul (contDiff_snd.comp contDiff_fst)))

private theorem slice_differential (f : DiskFunction) {z v : ℂ} (hz : z ∈ disk) (hv : v ∈ disk) (w : ℂ) :
    fderiv ℝ f.val (z,v) (0,w) = w * verticalSlope f (z,v) := by
  have hc := ((f.fibre z hz) v hv).differentiableAt (isOpen_ball.mem_nhds hv)
  have hs := (f.smooth.differentiable (by simp) (z,v)).hasFDerivAt
  have hd : HasFDerivAt (fun x : ℂ => f.val (z,x)) _ v := hs.comp v
    ((hasFDerivAt_const z v).prodMk (hasFDerivAt_id v))
  have h (d : ℂ) : fderiv ℝ (fun x => f.val (z,x)) v d = fderiv ℝ f.val (z,v) (0,d) :=
    congrArg (fun L : ℂ →L[ℝ] ℂ => L d) hd.fderiv
  unfold verticalSlope
  rw [← h, ← h, hc.fderiv_restrictScalars ℝ]
  change (fderiv ℂ (fun x => f.val (z,x)) v) w = w * (fderiv ℂ (fun x => f.val (z,x)) v) 1
  simpa only [smul_eq_mul, mul_one] using (fderiv ℂ (fun x => f.val (z,x)) v).map_smul w (1:ℂ)

private theorem product_quotient_interior (f : DiskFunction) {z w : ℂ} (hz : z ∈ disk) (hw : w ∈ disk) :
    w * quotient f (z,w) = f.val (z,w) - f.val (z,0) := by
  let ray (t : ℝ) := f.val (z, (t:ℂ) * w)
  have hs : ContDiff ℝ ∞ ray := f.smooth.comp (contDiff_const.prodMk (Complex.ofRealCLM.contDiff.mul contDiff_const))
  have hd (t : ℝ) (ht : t ∈ uIcc 0 1) : w * verticalSlope f (z,(t:ℂ)*w) = deriv ray t := by
    rw [uIcc_of_le zero_le_one] at ht
    have hi : (t:ℂ)*w ∈ disk := by
      rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
      exact (mul_le_of_le_one_left (norm_nonneg w) ht.2).trans_lt (mem_ball_zero_iff.mp hw)
    have htangent : HasDerivAt (fun s : ℝ => (s:ℂ)*w) w t := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).mul_const w
    have hpair : HasDerivAt (fun s : ℝ => (z, (s:ℂ)*w)) ((0,w):E) t :=
      (hasDerivAt_const t z).prodMk htangent
    have h : HasDerivAt ray _ t := (f.smooth.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt t hpair
    rw [h.deriv, slice_differential f hz hi]
  unfold quotient
  rw [← intervalIntegral.integral_const_mul, intervalIntegral.integral_congr hd,
    intervalIntegral.integral_deriv_eq_sub (fun t _ => hs.differentiable (by simp) t)
      ((hs.continuous_deriv (by simp)).intervalIntegrable _ _)]
  simp [ray]

/-- Smooth division by the fibre coordinate after subtracting its centre value,
with the identity valid on the unit circle as well. -/
theorem divide_at_zero (f : DiskFunction) : ∃ g : DiskFunction,
    ∀ z ∈ disk, ∀ w ∈ closedBall (0:ℂ) 1, w * g.val (z,w) = f.val (z,w) - f.val (z,0) := by
  have hs := smooth_quotient f
  have hc (z : ℂ) : Continuous (fun w => quotient f (z,w)) :=
    hs.continuous.comp (continuous_const.prodMk continuous_id)
  have hol (z : ℂ) (hz : z ∈ disk) : DifferentiableOn ℂ (fun w => quotient f (z,w)) disk := by
    apply (Complex.differentiableOn_compl_singleton_and_continuousAt_iff (c := 0)
      (isOpen_ball.mem_nhds (mem_ball_self one_pos))).mp
    refine ⟨?_, (hc z).continuousAt⟩
    let punct := disk \ {0}
    have H : DifferentiableOn ℂ (fun w => (f.val (z,w) - f.val (z,0)) / w) punct :=
      (((f.fibre z hz).mono diff_subset).sub (differentiableOn_const _)).div differentiableOn_id
        (fun _ h => h.2)
    apply H.congr
    intro w hw
    apply (eq_div_iff (show w ≠ 0 from hw.2)).mpr
    simpa [mul_comm] using product_quotient_interior f hz hw.1
  refine ⟨⟨quotient f, hs, hol⟩, ?_⟩
  intro z hz
  have closed : IsClosed {w : ℂ | w * quotient f (z,w) = f.val (z,w) - f.val (z,0)} := isClosed_eq (continuous_id.mul (hc z))
    ((f.smooth.continuous.comp (continuous_const.prodMk continuous_id)).sub continuous_const)
  have inc : disk ⊆ {w : ℂ | w * quotient f (z,w) = f.val (z,w) - f.val (z,0)} := fun w hw =>
    product_quotient_interior f hz hw
  have h := closure_minimal inc closed
  rw [show closure disk = closedBall (0:ℂ) 1 from closure_ball _ one_pos.ne'] at h
  exact fun _ hw => h hw


private def upper (u : ℂ → ℂ) (z : ℂ) : ℂ :=
  (fderiv ℝ u z 1 - I * fderiv ℝ u z I) / 2

private theorem split (u : ℂ → ℂ) (z : ℂ) (w : Circle) :
    (w:ℂ) * fderiv ℝ u z w = upper u z * (w:ℂ)^2 + twiceBar (fderiv ℝ u z) / 2 := by
  let L := fderiv ℝ u z
  have hv : (w:ℂ) = (w:ℂ).re • (1:ℂ) + (w:ℂ).im • I := by simp [Complex.real_smul]
  have hsplit : L w = ((w:ℂ).re:ℂ) * L 1 + ((w:ℂ).im:ℂ) * L I := by
    conv_lhs => rw [hv,map_add,map_smul,map_smul]
    rfl
  change (w:ℂ) * L w = (L 1 - I * L I) / 2 * (w:ℂ)^2 + (L 1 + I * L I) / 2
  rw [hsplit, Complex.re_eq_add_conj, Complex.im_eq_sub_conj]
  have hw : (w:ℂ) * conj (w:ℂ) = 1 := by rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; simp
  field_simp [Complex.I_ne_zero]
  linear_combination (norm := (ring_nf; simp [Complex.I_sq]))
    (I * L 1 - L I) * hw

private def baseFunction (u : ℂ → ℂ) (hu : ContDiff ℝ ∞ u) : DiskFunction where
  val p := u p.1
  smooth := hu.comp contDiff_fst
  fibre z _ := differentiableOn_const (u z)

private theorem transport_base (σ : ℂ → ℝ) (u : ℂ → ℂ) (hu : ContDiff ℝ ∞ u) (z : ℂ) (w : Circle) :
    boundaryTransport σ (baseFunction u hu).val z w = fderiv ℝ u z w := by
  have h := (hu.differentiable (by simp) z).hasFDerivAt.comp (z,(w:ℂ))
    (hasFDerivAt_fst (𝕜 := ℝ) (p := (z,(w:ℂ))))
  exact congrArg (fun L : E →L[ℝ] ℂ => L ((w:ℂ), (Isothermal.angularDrift σ z w : ℂ) * (I * w))) h.fderiv

/-- Every admissible source is an actual smooth fibre-holomorphic trace plus
the transport derivative of a smooth function of the base alone. -/
theorem split_source {rhs : TraceRHS} (h : ShiftExtends rhs) (σ : ℂ → ℝ) :
    ∃ b g : DiskFunction, ∀ z ∈ disk, ∀ w : Circle,
      rhs z w = boundaryTransport σ b.val z w + g.val (z,w) := by
  obtain ⟨f,hf⟩ := h
  obtain ⟨g,hg⟩ := divide_at_zero f
  obtain ⟨u,hu,heq⟩ := exists_twiceBar_primitive (fun z => 2 * f.val (z,0))
    (contDiff_const.mul (f.smooth.comp (contDiff_id.prodMk contDiff_const)))
  have hd := hu.fderiv_right (m := ∞) (by simp)
  have hupper : ContDiff ℝ ∞ (upper u) := ((hd.clm_apply contDiff_const).sub
    (contDiff_const.mul (hd.clm_apply contDiff_const))).div_const _
  let a := baseFunction (upper u) hupper
  refine ⟨baseFunction u hu, g.sub (a.mul velocity), ?_⟩
  intro z hz w
  rw [transport_base]
  have hcoeff := heq z (ball_subset_closedBall hz)
  have hsplit := split u z w
  rw [hcoeff] at hsplit
  have htrace := hg z hz (w:ℂ) (sphere_subset_closedBall w.property)
  rw [hf z hz] at htrace
  change rhs z w = fderiv ℝ u z w + (g.val (z,w) - upper u z * w)
  apply mul_left_cancel₀ (show (w:ℂ) ≠ 0 from Circle.coe_ne_zero w)
  linear_combination (norm := ring) -htrace -hsplit

/-- It suffices to invert the scalar geodesic derivative on the traces of
smooth fibre-holomorphic disk functions. This equivalence uses no metric hypotheses. -/
theorem scalarSolvability_iff (σ : ℂ → ℝ) : ScalarSolvability σ ↔
    ∀ g : DiskFunction, ∃ u : DiskFunction, ∀ z ∈ disk, ∀ w : Circle,
      boundaryTransport σ u.val z w = g.val (z,w) := by
  constructor
  · intro solve g
    exact solve _ (shifted_disk_function g)
  · intro solve rhs h
    obtain ⟨b,g,hg⟩ := split_source h σ
    obtain ⟨u,hu⟩ := solve g
    let f : DiskFunction := ⟨fun p => b.val p + u.val p, b.smooth.add u.smooth,
      fun z hz => (b.fibre z hz).add (u.fibre z hz)⟩
    refine ⟨f, ?_⟩
    intro z hz w
    rw [hg z hz, ← hu z hz]
    exact congrArg (fun L : E →L[ℝ] ℂ => L ((w:ℂ), (Isothermal.angularDrift σ z w : ℂ)*(I*w)))
      (((b.smooth.differentiable (by simp) (z,(w:ℂ))).hasFDerivAt.add
        (u.smooth.differentiable (by simp) (z,(w:ℂ))).hasFDerivAt).fderiv)

end TransportOkaGrauert.ScalarGeneral
