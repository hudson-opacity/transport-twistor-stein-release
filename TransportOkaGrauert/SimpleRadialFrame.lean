import TransportOkaGrauert.SimpleRadialColumns

/-! # The radial Hessian and the radial parallel frame on compact subdisks -/

noncomputable section
namespace TransportOkaGrauert.SimpleRadialFrame
open Complex Set Metric Filter SimpleDiskTarget SteinDivisor SimpleRadialColumns
open scoped ContDiff Topology ComplexConjugate

private theorem symmetric_from_radial {A : ℂ →L[ℝ] ℂ} {x : ℂ} (xn : x ≠ 0)
    (rad : A x = 0) {s : ℝ} (trans : A (I*x) = s • (I*x)) : (A I).re = (A 1).im := by
  have eq : x = x.re • (1:ℂ) + x.im • I := by simp [Complex.real_smul]
  have perp : I*x = -x.im • (1:ℂ) + x.re • I := by apply Complex.ext <;> simp [Complex.real_smul]
  rw [eq,map_add,map_smul,map_smul] at rad
  conv_lhs at trans => arg 2; rw [perp]
  rw [map_add,map_smul,map_smul] at trans
  have r₁ := congrArg Complex.re rad
  have r₂ := congrArg Complex.im rad
  have t₁ := congrArg Complex.re trans
  have t₂ := congrArg Complex.im trans
  simp only [Complex.real_smul, Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,Complex.zero_im,Complex.zero_re,
    zero_mul,one_mul,sub_zero,add_zero,zero_add,zero_sub] at r₁ r₂ t₁ t₂
  apply mul_left_cancel₀ (a := x.re^2+x.im^2) (by
    have h := normSq_pos.mpr xn
    nlinarith [show normSq x = x.re*x.re+x.im*x.im from rfl])
  linear_combination x.im*r₁ - x.re*r₂ + x.re*t₁ + x.im*t₂

variable {σ : ℂ → ℝ} {a : ℂ} (d : NormalChart σ a)

private def coordDiff (x : ℂ) := (fderiv ℝ d.L (d.f x)).comp (d.base x)

private def omega (x : ℂ) := (fderiv ℝ d.δ x).comp (coordDiff d x) -
  (fderiv ℝ σ (d.f x)).comp (((ContinuousLinearMap.mul ℝ ℂ) I).comp (d.base x))

private def defect (x : ℂ) := coordDiff d x + (omega d x).smulRight (I*x) - ContinuousLinearMap.id ℝ ℂ

private theorem target {x : ℂ} (hx : x ∈ d.D) : d.f x ∈ ball (0 : ℂ) 1 :=
  mem_ball_zero_iff.mpr (by simpa using hx 1 (right_mem_Icc.mpr zero_le_one))

private theorem regularity (hs : ContDiff ℝ ∞ σ) : ContDiffOn ℝ ∞ (defect d) d.D ∧
    ContDiffOn ℝ ∞ (omega d) d.D := by
  have co (x : ℂ) (hx : x ∈ d.D) : ContDiffAt ℝ ∞ (coordDiff d) x :=
    (((d.sL.contDiffAt (isOpen_ball.mem_nhds (target d hx))).fderiv_right (m := ∞) (by simp)).comp
      x d.sf.contDiffAt).clm_comp ((d.base_smooth hs).contDiffAt)
  have om (x : ℂ) (hx : x ∈ d.D) : ContDiffAt ℝ ∞ (omega d) x :=
    (((d.sd.fderiv_right (m := ∞) (by simp)).contDiffAt).clm_comp (co x hx)).sub
      ((((hs.fderiv_right (m := ∞) (by simp)).comp d.sf).contDiffAt).clm_comp
        (contDiffAt_const.clm_comp (d.base_smooth hs).contDiffAt))
  refine ⟨fun x hx => ?_, fun x hx => (om x hx).contDiffWithinAt⟩
  exact (((co x hx).add ((om x hx).smulRight (contDiffAt_const.mul contDiffAt_id))).sub contDiffAt_const).contDiffWithinAt

private theorem inverse_jet {x : ℂ} (hx : x ∈ d.D) (u : ℂ) :
    fderiv ℝ d.L (d.f x) (fderiv ℝ d.f x u) = u := by
  have left : d.L ∘ d.f =ᶠ[𝓝 x] id := by
    filter_upwards [d.openD.mem_nhds hx] with z hz
    exact d.left z (fun t ht => (hz t ht).le) (target d hz)
  have h := (((d.sL.contDiffAt (isOpen_ball.mem_nhds (target d hx))).differentiableAt (by simp)).hasFDerivAt.comp
    x (d.sf.differentiable (by simp) x).hasFDerivAt).fderiv
  have eq := h.symm.trans left.fderiv_eq
  simpa using DFunLike.congr_fun eq u

private theorem radial_kernel (simple : SimpleMetric σ) {x : ℂ} (hx : x ∈ d.D) :
    defect d x x = 0 ∧ omega d x x = 0 := by
  by_cases hn : x = 0
  · simp [hn]
  obtain ⟨rad,phase,_⟩ := d.polar_columns simple hx hn
  have co : coordDiff d x x = x := by
    change fderiv ℝ d.L (d.f x) (d.base x x) = _
    rw [← rad,inverse_jet d hx]
  have om : omega d x x = 0 := by
    change fderiv ℝ d.δ x (coordDiff d x x) - fderiv ℝ σ (d.f x) (I * d.base x x) = 0
    rw [co,phase,sub_self]
  exact ⟨by change coordDiff d x x + omega d x x • (I*x) - x = 0; rw [co,om,zero_smul,add_zero,sub_self],om⟩

private theorem symmetric (simple : SimpleMetric σ) (x : ℂ) (hx : x ∈ d.D) :
    (defect d x I).re = (defect d x 1).im := by
  have away (z : ℂ) (hz : z ∈ d.D) (hn : z ≠ 0) :
      (defect d z I).re = (defect d z 1).im := by
    obtain ⟨_,_,k,hk,angular⟩ := d.polar_columns simple hz hn
    have co : coordDiff d z (I*z) = k⁻¹ • (I*z) := by
      have eq := inverse_jet d hz (I*z)
      rw [angular,map_smul] at eq
      change fderiv ℝ d.L (d.f z) (d.base z (I*z)) = _
      calc
        _ = k⁻¹ • (k • fderiv ℝ d.L (d.f z) (d.base z (I*z))) := (inv_smul_smul₀ hk.ne' _).symm
        _ = _ := congrArg (fun v : ℂ => k⁻¹ • v) eq
    apply symmetric_from_radial hn (radial_kernel d simple hz).1
      (s := k⁻¹ + omega d z (I*z) - 1)
    change coordDiff d z (I*z) + omega d z (I*z) • (I*z) - I*z = _
    rw [co,sub_smul,add_smul,one_smul]
  by_cases hn : x = 0
  · subst x
    have h := (regularity d simple.smooth).1.contDiffAt (d.openD.mem_nhds hx)
    apply tendsto_nhds_unique_of_eventuallyEq (l := 𝓝[≠] (0:ℂ))
      ((Complex.continuous_re.continuousAt.comp (h.continuousAt.clm_apply continuousAt_const)).tendsto.mono_left nhdsWithin_le_nhds)
      ((Complex.continuous_im.continuousAt.comp (h.continuousAt.clm_apply continuousAt_const)).tendsto.mono_left nhdsWithin_le_nhds)
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (d.openD.mem_nhds hx)] with z hz hD
    exact away z hD hz
  · exact away x hx hn

/-- The equations before changing the scale of a subdisk to the fixed unit disk. -/
structure Fields (σ : ℂ → ℝ) (a : ℂ) (S : Set ℂ) where
  W : ℂ → ℂ
  ρ : ℂ → ℂ
  c : ℂ → ℝ
  k : ℂ → ℝ
  smoothW : ContDiff ℝ ∞ W
  smoothρ : ContDiff ℝ ∞ ρ
  smoothC : ContDiff ℝ ∞ c
  smoothK : ContDiff ℝ ∞ k
  unitρ : ∀ z ∈ S, ‖ρ z‖ = 1
  zeroW : ∀ z ∈ S, W z = 0 ↔ z = a
  hessian : ∀ z ∈ S, ∀ w : ℂ, fderiv ℝ W z w =
    (Real.exp (σ z) : ℂ) * rankOneHessian (c z) (W z) (ρ z*w) -
      I * PencilGeometry.connection σ k W ρ z w * W z
  radialFrame : ∀ z ∈ S, ∀ w : ℂ, fderiv ℝ ρ z w =
    -I * ((PencilGeometry.connection σ k W ρ z w : ℂ) + fderiv ℝ σ z (I*w)) * ρ z

private def back (t : ℝ) : ℂ := Circle.exp (-t)

private theorem back_smooth : ContDiff ℝ ∞ back :=
  ((Complex.ofRealCLM.contDiff.comp contDiff_neg).mul (contDiff_const (c := I))).cexp

private theorem back_deriv (t : ℝ) : HasDerivAt back (-I * back t) t := by
  change HasDerivAt (fun s : ℝ => (Circle.exp (-s) : ℂ)) (-I * (Circle.exp (-t) : ℂ)) t
  simpa only [id_eq, Function.comp_def, neg_smul, one_smul, neg_mul] using
    (SimpleRadialVariation.angle_velocity (-t)).scomp t (hasDerivAt_id t).neg

private theorem inner_scale (p w : ℂ) (e : ℝ) :
    longitudinal p (e • w) = e * longitudinal p w := by
  simp [longitudinal, Complex.real_smul, Complex.mul_re,Complex.mul_im]
  ring

private theorem quarter (p w : ℂ) : longitudinal (I*p) w = -transverse p w := by
  simp [longitudinal,transverse,Complex.mul_re,Complex.mul_im]

/-- Every compact subset of the open disk has ambient smooth representatives
of the distance gradient, oriented radial frame and both scalar coefficients.
The centre may belong to the compact set. -/
theorem fields_on_compact {σ : ℂ → ℝ} (simple : SimpleMetric σ) {a : ℂ} (ha : ‖a‖ < 1)
    {S : Set ℂ} (compact : IsCompact S) (inside : S ⊆ ball (0 : ℂ) 1) : Nonempty (Fields σ a S) := by
  let d := SimpleRadialColumns.chart simple ha
  let K := d.L '' S
  have hK : IsCompact K := compact.image_of_continuousOn (d.sL.continuousOn.mono inside)
  have Kd : K ⊆ d.D := by rintro _ ⟨z,hz,rfl⟩; exact d.inD (inside hz) simple ha
  obtain ⟨C,N,sC,sN,form⟩ := SimpleRadialDivision.coefficients d.openD hK.isClosed Kd
    (defect d) (omega d) (regularity d simple.smooth).1 (regularity d simple.smooth).2
    (fun x hx => (radial_kernel d simple hx).1) (fun x hx => (radial_kernel d simple hx).2)
    (symmetric d simple)
  obtain ⟨W,sW,germ⟩ := SimpleRadialDivision.extend isOpen_ball compact.isClosed inside d.sL
  let ρ (z : ℂ) := back (d.δ (W z))
  let c := C ∘ W
  let k := N ∘ W
  have sρ : ContDiff ℝ ∞ ρ := back_smooth.comp (d.sd.comp sW)
  have laws (z : ℂ) (hz : z ∈ S) (w : ℂ) :
      fderiv ℝ W z w =
        (Real.exp (σ z) : ℂ) * rankOneHessian (c z) (W z) (ρ z*w) -
          I * PencilGeometry.connection σ k W ρ z w * W z ∧
      fderiv ℝ ρ z w =
        -I * ((PencilGeometry.connection σ k W ρ z w : ℂ) + fderiv ℝ σ z (I*w)) * ρ z := by
    let x := W z
    let e := Real.exp (σ z)
    let v := ρ z * w
    let u := e • v
    let γ := PencilGeometry.connection σ k W ρ z w
    have wx : x = d.L z := (germ z hz).self_of_nhds
    have fx : d.f x = z := wx ▸ (d.right z (inside hz)).2
    have inK : x ∈ K := ⟨z,hz,wx.symm⟩
    have fw : d.frame x * ρ z = 1 := by
      change (Circle.exp (d.δ x) : ℂ) * (Circle.exp (-(d.δ x)) : ℂ) = 1
      rw [← Circle.coe_mul, ← Circle.exp_add, add_neg_cancel]
      simp
    have bv : d.base x u = w := by
      change (↑(Real.exp (-σ (d.f x))) * d.frame x) * (e • (ρ z * w)) = w
      rw [fx, Real.exp_neg, Complex.real_smul]
      have he : (e : ℂ) ≠ 0 := by exact_mod_cast Real.exp_ne_zero (σ z)
      change ((↑(e⁻¹) : ℂ) * d.frame x) * ((e:ℂ) * (ρ z*w)) = w
      rw [Complex.ofReal_inv]
      calc
        _ = ((e : ℂ)⁻¹ * (e : ℂ)) * ((d.frame x * ρ z) * w) := by ring
        _ = _ := by rw [inv_mul_cancel₀ he,fw,one_mul,one_mul]
    have co : coordDiff d x u = fderiv ℝ W z w := by
      change fderiv ℝ d.L (d.f x) (d.base x u) = _
      rw [fx,bv,(germ z hz).fderiv_eq]
    obtain ⟨A,B⟩ := form x inK u
    have om : omega d x u = γ := by
      rw [B, inner_scale, quarter]
      change N x * (e * -transverse x v) = -(e * N x) * transverse x v
      ring
    have hγ : fderiv ℝ d.δ x (fderiv ℝ W z w) = γ + fderiv ℝ σ z (I*w) := by
      change fderiv ℝ d.δ x (coordDiff d x u) - fderiv ℝ σ (d.f x) (I * d.base x u) = γ at om
      rw [co,fx,bv] at om
      linarith
    constructor
    · change coordDiff d x u + omega d x u • (I*x) - u =
        (C x * longitudinal (I*x) u) • (I*x) at A
      rw [co,om, inner_scale] at A
      change fderiv ℝ W z w = (e:ℂ) * (v + ↑(C x * longitudinal (I*x) v) * (I*x)) - I * (γ:ℂ) * x
      simp only [u, Complex.real_smul, Complex.ofReal_mul] at A ⊢
      linear_combination A
    · have h := (back_deriv (d.δ x)).hasFDerivAt.comp z
        ((d.sd.differentiable (by simp) x).hasFDerivAt.comp z (sW.differentiable (by simp) z).hasFDerivAt)
      change HasFDerivAt ρ _ z at h
      rw [h.fderiv]
      change fderiv ℝ d.δ x (fderiv ℝ W z w) • (-I * ρ z) =
        -I * ((γ:ℂ) + ↑(fderiv ℝ σ z (I*w))) * ρ z
      rw [hγ,Complex.real_smul,Complex.ofReal_add]
      ring
  refine ⟨⟨W,ρ,c,k,sW,sρ,sC.comp sW,sN.comp sW,fun _ _ => Circle.norm_coe _,?_,
    fun z hz w => (laws z hz w).1,fun z hz w => (laws z hz w).2⟩⟩
  intro z hz
  rw [(germ z hz).self_of_nhds]
  constructor
  · intro h
    have r := (d.right z (inside hz)).2
    rw [h,d.centre] at r
    exact r.symm
  · rintro rfl
    have r : (0:ℂ) ∈ SimpleRadialStar.retained d.f 1 := fun t _ => by simpa [d.centre] using ha.le
    simpa [d.centre] using d.left 0 r (by rw [d.centre]; exact mem_ball_zero_iff.mpr ha)

end TransportOkaGrauert.SimpleRadialFrame
