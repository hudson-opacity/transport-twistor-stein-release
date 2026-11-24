import TransportOkaGrauert.ScalarRiccati
import TransportOkaGrauert.ScalarLiouville
import TransportOkaGrauert.ScalarBoundaryRay

/-! # Scalar Pestov estimate over a simple disk -/
noncomputable section
namespace TransportOkaGrauert.ScalarPestov
open SimpleDiskTarget ScalarLiouville FrameLevi ConformalFrame Set MeasureTheory Filter
open scoped ContDiff Topology

theorem energy_estimate {σ : ℂ → ℝ} (simple : SimpleMetric σ) {u : Chart → ℝ}
    (hu : ContDiff ℝ ∞ u) (pu : periodic u) (zu : zero_exterior u) :
    integral σ (fun p => speed σ u p ^ 2) ≤ integral σ (fun p => vertical (speed σ u) p ^ 2) := by
  obtain ⟨r,pr,good⟩ := strict_riccati simple
  let A := speed σ u
  let B := horizontal σ u
  let C := vertical u
  have hs := simple.smooth
  have hX := (smooth_XH hs).1
  have hH := (smooth_XH hs).2
  have hV : ContDiff ℝ ∞ V := contDiff_const
  have a : ContDiff ℝ ∞ A := smooth_along hX hu
  have b : ContDiff ℝ ∞ B := smooth_along hH hu
  have c : ContDiff ℝ ∞ C := smooth_along hV hu
  have pa : periodic A := periodic_along _ (periodic_X σ) pu
  have pb : periodic B := periodic_along _ (periodic_H σ) pu
  have pc : periodic C := periodic_along _ (fun _ => rfl) pu
  have za : zero_exterior A := exterior_along _ zu
  have zc : zero_exterior C := exterior_along _ zu
  let fV (p : Chart) := A p * B p
  let fX (p : Chart) := C p * B p + r p * (C p * C p)
  let fH (p : Chart) := A p * C p
  have sfV : ContDiff ℝ ∞ fV := a.mul b
  have sfH : ContDiff ℝ ∞ fH := a.mul c
  have zV : zero_exterior fV := fun p hp => by simp [fV,za p hp]
  have zX : zero_exterior fX := fun p hp => by simp [fX,zc p hp]
  have zH : zero_exterior fH := fun p hp => by simp [fH,za p hp]
  have sfX : ContDiff ℝ ∞ fX := by
    apply contDiff_iff_contDiffAt.mpr
    intro p
    by_cases h : ‖p.1‖ ≤ 1
    · exact (c.contDiffAt.mul b.contDiffAt).add ((good p h).1.mul (c.contDiffAt.mul c.contDiffAt))
    · exact contDiffAt_const.congr_of_eventuallyEq ((continuous_fst.norm.continuousAt.eventually_const_lt
        (lt_of_not_ge h)).mono fun y hy => zX y hy)
  have iV := integral_vertical hs sfV (fun p => by simp [fV,pa p,pb p]) zV
  have iX := integral_X hs sfX (fun p => by simp [fX,pc p,pb p,show r (shift p) = r p from pr p]) zX
  have iH := integral_H hs sfH (fun p => by simp [fH,pa p,pc p]) zH
  let va := vertical A
  let vF := vertical fV
  let xF := speed σ fX
  let hF := horizontal σ fH
  have hVa : ContDiff ℝ ∞ va := smooth_along hV a
  have hvF : ContDiff ℝ ∞ vF := smooth_along hV sfV
  have hxF : ContDiff ℝ ∞ xF := smooth_along hX sfX
  have hhF : ContDiff ℝ ∞ hF := smooth_along hH sfH
  have pt (p : Chart) : A p ^ 2 ≤ va p ^ 2 - vF p - xF p + hF p := by
    by_cases hp : ‖p.1‖ ≤ 1
    · have qr := (good p hp).1.differentiableAt (by simp)
      have qa := a.differentiable (by simp) p
      have qb := b.differentiable (by simp) p
      have qc := c.differentiable (by simp) p
      have e := flux_identity hs hu p
      change va p ^ 2 - speed σ C p ^ 2 = A p ^ 2 - curvature σ p.1 * C p ^ 2 +
        vF p + speed σ (fun q => C q * B q) p - hF p at e
      have er : xF p = speed σ (fun q => C q * B q) p +
          speed σ r p * (C p * C p) + r p * (2 * C p * speed σ C p) := by
        change fderiv ℝ (fun q => C q * B q + r q * (C q * C q)) p (X σ p) = _
        rw [fderiv_fun_add (f := fun q => C q * B q) (g := fun q => r q * (C q * C q))
          (qc.mul qb) (qr.mul (qc.mul qc)),ContinuousLinearMap.add_apply]
        change along (X σ) (fun q => C q * B q) p + along (X σ) (fun q => r q * (C q * C q)) p = _
        rw [product_rule (X σ) (g := fun q => C q * C q) qr (qc.mul qc),product_rule (X σ) qc qc]
        simp only [speed]; ring
      have margin := mul_nonpos_of_nonpos_of_nonneg (good p hp).2.le (sq_nonneg (C p))
      nlinarith [sq_nonneg (speed σ C p - r p * C p)]
    · have ho := lt_of_not_ge hp
      have zV' := exterior_along V zV p ho
      have zX' := exterior_along (X σ) zX p ho
      have zH' := exterior_along (H σ) zH p ho
      change vF p = 0 at zV'
      change xF p = 0 at zX'
      change hF p = 0 at zH'
      simpa [za p ho,zV',zX',zH'] using (sq_nonneg (va p))
  let w := fun x => areaDensity σ (point x)
  have cw : Continuous w := (continuous_const.mul (hs.continuous.comp (continuous_fst.comp point.continuous))).rexp
  have ig {f : Chart → ℝ} (hf : Continuous f) :
      IntegrableOn (fun x => w x * f (point x)) box :=
    (cw.mul (hf.comp point.continuous)).continuousOn.integrableOn_compact isCompact_Icc
  have ine := integral_mono (ig (a.continuous.pow 2))
    (ig ((((hVa.continuous.pow 2).sub hvF.continuous).sub hxF.continuous).add hhF.continuous))
    (fun x => mul_le_mul_of_nonneg_left (pt (point x)) (Real.exp_pos _).le)
  change integral σ (fun p => A p ^ 2) ≤ integral σ (fun p => va p ^ 2 - vF p - xF p + hF p) at ine
  rw [int_linear hs.continuous ((hVa.continuous.pow 2).sub hvF.continuous) hxF.continuous hhF.continuous,
    show integral σ xF = 0 from iX,show integral σ hF = 0 from iH,sub_zero,add_zero] at ine
  have red : integral σ (fun p => va p ^ 2 - vF p) = integral σ (fun p => va p ^ 2) := by
    have z := int_linear hs.continuous (hVa.continuous.pow 2) hvF.continuous (continuous_const (y := (0:ℝ)))
    have z₀ : integral σ (fun _ => 0) = 0 := by simp [ScalarLiouville.integral]
    simpa only [add_zero,show integral σ vF = 0 from iV,z₀,sub_zero,Pi.pow_apply] using z
  rwa [red] at ine

/-- A base function which is the speed derivative of a periodic compactly
supported smooth function on the unit tangent bundle vanishes. -/
theorem base_coboundary_injective {σ : ℂ → ℝ} (simple : SimpleMetric σ) {u : Chart → ℝ}
    (hu : ContDiff ℝ ∞ u) (pu : periodic u) (zu : zero_exterior u) {f : ℂ → ℝ}
    (hf : ContDiff ℝ ∞ f) (eq : ∀ p, speed σ u p = f p.1) :
    ∀ z : ℂ, ‖z‖ ≤ 1 → f z = 0 := by
  let A := speed σ u
  have hd : A = fun p : Chart => f p.1 := funext eq
  have va (p : Chart) : vertical A p = 0 := by
    rw [hd]; unfold vertical along
    rw [show fderiv ℝ (fun q : Chart => f q.1) p = _ from
      ((hf.differentiable (by simp) p.1).hasFDerivAt.comp p (hasFDerivAt_fst ..)).fderiv]
    simp [V]
  have ine := energy_estimate simple hu pu zu
  change integral σ (fun p => A p ^ 2) ≤ integral σ (fun p => vertical A p ^ 2) at ine
  simp only [va,zero_pow (by decide : 2 ≠ 0),ScalarLiouville.integral,mul_zero,integral_zero] at ine
  rw [hd] at ine
  let e := fun x : BoxSpace => areaDensity σ (point x) * f (point x).1 ^ 2
  have hbase := continuous_fst.comp point.continuous
  have ce : Continuous e := (continuous_const.mul (simple.smooth.continuous.comp hbase)).rexp.mul ((hf.continuous.comp hbase).pow 2)
  have pos (x : BoxSpace) : 0 ≤ e x := mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  have zero : (∫ x in box, e x) = 0 := le_antisymm ine (integral_nonneg pos)
  have ie : IntegrableOn e box := ce.continuousOn.integrableOn_compact isCompact_Icc
  have ae := (integral_eq_zero_iff_of_nonneg pos ie).mp zero
  let U : Set BoxSpace := Set.pi univ (fun i => Ioo (lo i) (hi i))
  have ou : IsOpen U := isOpen_set_pi finite_univ (fun _ _ => isOpen_Ioo)
  have sub : U ⊆ box := fun x hx =>
    ⟨fun i => (hx i trivial).1.le,fun i => (hx i trivial).2.le⟩
  have eqU := Measure.eqOn_open_of_ae_eq (ae_restrict_of_ae_restrict_of_subset sub ae) ou
    ce.continuousOn continuousOn_const
  intro z hz
  let x : BoxSpace := ![z.re,z.im,0]
  have hRe := abs_le.mp ((Complex.abs_re_le_norm z).trans hz)
  have hIm := abs_le.mp ((Complex.abs_im_le_norm z).trans hz)
  have hx : x ∈ U := by
    intro i _
    fin_cases i <;> simp [lo,hi,x,Real.pi_pos] <;> constructor <;> linarith
  have ep := eqU hx
  change areaDensity σ (point x) * f (point x).1 ^ 2 = 0 at ep
  have ex : (point x).1 = z := by apply Complex.ext <;> simp [x,point_apply]
  rw [ex] at ep
  have zz := (mul_eq_zero.mp ep).resolve_left (Real.exp_pos _).ne'
  nlinarith [sq_nonneg (f z)]

/-- Vanishing scalar ray integrals force the source to vanish. The geodesics
are those of a complete convex extension of the prescribed simple disk. -/
theorem scalar_ray_injective {σ : ℂ → ℝ} (simple : SimpleMetric σ) (F : JacobiEnlargement.Flow σ)
    {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f) (off : ∀ z, 1 < ‖z‖ → f z = 0)
    (null : ∀ p t, 0 < t → 1 < ‖p.1‖ → 1 < ‖F.base p t‖ → ScalarRayPrimitive.ray F f p t = 0) :
    f = 0 := by
  obtain ⟨u,hu,pu,zu,eq⟩ := ScalarRayPrimitive.exists_supported_primitive simple F hf off null
  let U := u ∘ PolarCollar.direction
  have hU : ContDiff ℝ ∞ U := hu.comp PolarCollar.direction.contDiff
  have pU : periodic U := fun p => pu (PolarCollar.direction p) (2*Real.pi) Circle.exp_two_pi
  have zU : zero_exterior U := fun p hp => zu (PolarCollar.direction p) hp
  have eU (p : Chart) : speed σ U p = f p.1 := by
    have push : PolarCollar.direction (X σ p) = PathContinuation.chartVector σ (PolarCollar.direction p) :=
      congrFun (PhysicalJacobiWeight.projected_X σ) (PolarCollar.direction p)
    change fderiv ℝ (u ∘ PolarCollar.direction) p (X σ p) = _
    rw [fderiv_comp p (hu.differentiable (by simp) _) (PolarCollar.direction.differentiableAt),
      ContinuousLinearMap.fderiv,ContinuousLinearMap.comp_apply,push]
    exact eq (PolarCollar.direction p)
  have inDisk := base_coboundary_injective simple hU pU zU hf eU
  funext z
  by_cases h : ‖z‖ ≤ 1
  · exact inDisk z h
  · exact off z (lt_of_not_ge h)

/-- Intrinsic scalar X-ray injectivity for an arbitrary simple conformal
metric. Only boundary-to-boundary geodesics within the disk are measured. -/
theorem boundary_ray_injective {σ : ℂ → ℝ} (simple : SimpleMetric σ) {f : ℂ → ℝ}
    (hf : ContDiff ℝ ∞ f) (off : ∀ z, 1 < ‖z‖ → f z = 0)
    (null : ScalarRayPrimitive.boundary_ray_zero σ f) : f = 0 := by
  obtain ⟨F⟩ := JacobiEnlargement.exists_flow simple
  exact scalar_ray_injective simple F hf off
    (ScalarRayPrimitive.extension_ray_zero F hf.continuous off null)

end TransportOkaGrauert.ScalarPestov
