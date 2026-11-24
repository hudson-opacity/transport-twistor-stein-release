import TransportOkaGrauert.ChartPencils

/-!
# From the distance Hessian and radial connection to the pencil sources

The radius vector and radial parallel frame are geometric inputs. Their covariant
derivative equations are expressed below using ordinary base derivatives.
The two geodesic derivatives and the smooth disk extension of the shifted
attenuation are derived from those equations. For a simple metric, the outstanding
geometric construction is the family of squared-distance gradients and radial
parallel frames (with smooth ambient representatives), together with their two
coefficient functions and the endpoint alignment used below.
-/

noncomputable section

namespace TransportOkaGrauert.PencilGeometry

open Complex ChartStein ChartCorrespondence PencilLifts ChartPencils SteinDivisor
open scoped ContDiff ComplexConjugate

/-- Connection speed along the unscaled boundary vector. The factor exp(σ) converts
from the metric unit speed used in the Hessian equation. -/
def connection (σ k : ℂ → ℝ) (W ρ : ℂ → ℂ) (z w : ℂ) : ℝ :=
  -(Real.exp (σ z) * k z) * transverse (W z) (ρ z * w)

/-- The distance-gradient field in a radial parallel frame, its rotation relative
to the isothermal frame, and the two real coefficient functions. -/
structure Data (σ : ℂ → ℝ) (a : ClosedDisk) where
  W : ℂ → ℂ
  ρ : ℂ → ℂ
  c : ℂ → ℝ
  k : ℂ → ℝ
  smoothW : ContDiff ℝ ∞ W
  smoothρ : ContDiff ℝ ∞ ρ
  smoothC : ContDiff ℝ ∞ c
  smoothK : ContDiff ℝ ∞ k
  unitρ : ∀ z : ClosedDisk, ‖ρ z.val‖ = 1
  zeroW : ∀ z : ClosedDisk, W z.val = 0 ↔ z = a
  hessian : ∀ z : ClosedDisk, ∀ w : Circle, fderiv ℝ W z.val (w:ℂ) =
    (Real.exp (σ z) : ℂ) * rankOneHessian (c z) (W z) (ρ z * w) -
      I * connection σ k W ρ z w * W z
  radialFrame : ∀ z ∈ disk, ∀ w : Circle, fderiv ℝ ρ z (w:ℂ) =
    -I * ((connection σ k W ρ z w : ℂ) + Isothermal.angularDrift σ z w) * ρ z

/-- At the centre the covariant Hessian is the identity. In complex frame
coordinates its ordinary derivative multiplies by the conformal scale and rotation. -/
theorem center_derivative {σ a} (d : Data σ a) : Function.Injective (fderiv ℝ d.W a.val) := by
  have hW := (d.zeroW a).mpr rfl
  have unit (w : Circle) : fderiv ℝ d.W a.val (w:ℂ) =
      (Real.exp (σ a.val) : ℂ) * (d.ρ a.val * w) := by
    simpa [hW, rankOneHessian, longitudinal] using d.hessian a w
  let i : Circle := ⟨I, mem_sphere_zero_iff_norm.mpr Complex.norm_I⟩
  have h1 : fderiv ℝ d.W a.val 1 = (Real.exp (σ a.val) : ℂ) * (d.ρ a.val * 1) := unit 1
  have hi : fderiv ℝ d.W a.val I = (Real.exp (σ a.val) : ℂ) * (d.ρ a.val * I) := unit i
  have act (v : ℂ) : fderiv ℝ d.W a.val v = (Real.exp (σ a.val) : ℂ) * d.ρ a.val * v := by
    have hv : v = v.re • (1:ℂ) + v.im • I := by simp [Complex.real_smul]
    conv_lhs => rw [hv,map_add,map_smul,map_smul,h1,hi]
    conv_rhs => rw [hv]
    simp only [Complex.real_smul]
    ring
  have he : (Real.exp (σ a.val) : ℂ) ≠ 0 := by exact_mod_cast Real.exp_ne_zero (σ a.val)
  have hr : d.ρ a.val ≠ 0 := norm_ne_zero_iff.mp ((d.unitρ a).trans_ne one_ne_zero)
  intro u v huv
  rw [act,act] at huv
  exact mul_left_cancel₀ (mul_ne_zero he hr) huv

/-- The source of both angular modes before multiplication by the velocity. -/
def source {σ a} (d : Data σ a) (z : ℂ) (w : Circle) : ℂ :=
  I * connection σ d.k d.W d.ρ z w +
    ↑(Real.exp (σ z) * d.c z * longitudinal (d.W z) (d.ρ z * w))

private def b {σ a} (hs : ContDiff ℝ ∞ σ) (d : Data σ a) : DiskFunction where
  val p := ((Real.exp (σ p.1) * d.k p.1 / 2 : ℝ) : ℂ)
  smooth := Complex.ofRealCLM.contDiff.comp (((hs.comp contDiff_fst).exp.mul
    (d.smoothK.comp contDiff_fst)).div_const 2)
  fibre z _ := by
    exact differentiableOn_const ((Real.exp (σ z) * d.k z / 2 : ℝ) : ℂ)

private theorem unit_product {σ a} (d : Data σ a) {z : ℂ} (hz : z ∈ disk) (w : Circle) :
    (d.ρ z * w) * conj (d.ρ z * w) = 1 := by
  have hρ := d.unitρ ⟨z, Metric.ball_subset_closedBall hz⟩
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_mul, hρ]
  simp

private theorem polynomial_trace (a b T w : ℂ) (hw : w * conj w = 1) :
    ((a-b)*T+(a+b)*conj T*w^2)/2 =
      w*(-I*b*((T*conj w).im : ℂ)+a*((T*conj w).re : ℂ)) := by
  simp only [Complex.re_eq_add_conj, Complex.im_eq_sub_conj, map_mul, starRingEnd_self_apply]
  field_simp [Complex.I_ne_zero]
  linear_combination -(a-b)*T*hw

private theorem source_extends {σ a} (hs : ContDiff ℝ ∞ σ) (d : Data σ a) :
    ShiftExtends (source d) := by
  let α (z : ℂ) : ℂ := ↑(Real.exp (σ z) * d.c z : ℝ)
  let β (z : ℂ) : ℂ := ↑(Real.exp (σ z) * d.k z : ℝ)
  let T (z : ℂ) := d.W z * conj (d.ρ z)
  have hα : ContDiff ℝ ∞ α := Complex.ofRealCLM.contDiff.comp (hs.exp.mul d.smoothC)
  have hβ : ContDiff ℝ ∞ β := Complex.ofRealCLM.contDiff.comp (hs.exp.mul d.smoothK)
  have hT : ContDiff ℝ ∞ T := d.smoothW.mul (Complex.conjCLE.contDiff.comp d.smoothρ)
  let f (p : E) := ((α p.1 - β p.1) * T p.1 + (α p.1 + β p.1) * conj (T p.1) * p.2^2)/2
  refine ⟨⟨f, ?_, ?_⟩, ?_⟩
  · unfold f
    exact ((((hα.sub hβ).mul hT).comp contDiff_fst).add
      ((((hα.add hβ).mul (Complex.conjCLE.contDiff.comp hT)).comp contDiff_fst).mul
        (contDiff_snd.pow 2))).div_const 2
  · intro z _
    exact (((differentiableOn_const ((α z - β z)*T z)).add ((differentiableOn_const ((α z + β z)*conj (T z))).mul
      ((differentiableOn_id (s := disk)).pow 2)))).div_const 2
  · intro z _ w
    have hw : (w:ℂ) * conj (w:ℂ) = 1 := by rw [Complex.mul_conj,Complex.normSq_eq_norm_sq]; simp
    have hu : d.W z * conj (d.ρ z * (w:ℂ)) = T z * conj (w:ℂ) := by simp [T,mul_assoc]
    change f (z,(w:ℂ)) = _
    change ((α z - β z) * T z + (α z + β z) * conj (T z) * (w:ℂ)^2)/2 = _
    have rhs : source d z w =
        -I*β z*((T z*conj (w:ℂ)).im : ℂ) + α z*((T z*conj (w:ℂ)).re : ℂ) := by
      simp only [source, connection, transverse, longitudinal, hu, α, β, Complex.ofReal_mul,
        Complex.ofReal_neg]
      ring
    rw [rhs]
    exact polynomial_trace (α z) (β z) (T z) (w:ℂ) hw

private theorem derivative_m {σ a} (d : Data σ a) {z : ℂ} (hz : z ∈ disk) (w : Circle) :
    boundaryTransport σ (moving d.ρ d.smoothρ).val z w =
      -I * (connection σ d.k d.W d.ρ z w : ℂ) * (d.ρ z * w) := by
  let p : E := (z,w)
  have hd := (((d.smoothρ.differentiable (by simp) z).hasFDerivAt.comp p
    (hasFDerivAt_fst (𝕜 := ℝ) (p := p))).mul (hasFDerivAt_snd (𝕜 := ℝ) (p := p)))
  unfold boundaryTransport ChartCorrespondence.slope
  rw [show fderiv ℝ (moving d.ρ d.smoothρ).val (z,(w:ℂ)) = _ from hd.fderiv]
  simp [p, d.radialFrame z hz w, smul_eq_mul]
  ring

private theorem derivative_q {σ a} (d : Data σ a) {z : ℂ} (hz : z ∈ disk) (w : Circle) :
    boundaryTransport σ (radial d.W d.ρ d.smoothW d.smoothρ).val z w =
      -source d z w * (radial d.W d.ρ d.smoothW d.smoothρ).val (z,w) := by
  let p : E := (z,w)
  let m := moving d.ρ d.smoothρ
  let μ := d.ρ z * (w:ℂ)
  let Δ := d.W z
  let κ := rankOneHessian (d.c z) Δ μ
  let A : ℂ := Real.exp (σ z)
  let γ : ℂ := connection σ d.k d.W d.ρ z w
  let Q := radial d.W d.ρ d.smoothW d.smoothρ
  let v : E := ((w:ℂ), (Isothermal.angularDrift σ z w : ℂ) * (I*w))
  have hdW := (d.smoothW.differentiable (by simp) z).hasFDerivAt.comp p (hasFDerivAt_fst (𝕜 := ℝ) (p := p))
  have hdC := Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp p hdW
  have hd := hdW.sub (((m.smooth.differentiable (by simp) p).hasFDerivAt.pow 2).mul hdC)
  have dq : boundaryTransport σ Q.val z w =
      fderiv ℝ d.W z (w:ℂ) -
        (μ^2 * conj (fderiv ℝ d.W z (w:ℂ)) + conj Δ*(2*μ*boundaryTransport σ m.val z w)) := by
    change fderiv ℝ Q.val p v = _
    rw [show fderiv ℝ Q.val p = _ from hd.fderiv]
    simp [m,p,v,μ,Δ,boundaryTransport,ChartCorrespondence.slope,moving,smul_eq_mul,two_smul]
    ring_nf
    simp
  have unit := unit_product d hz w
  have hess : FlatScalar.firstIntegral κ μ =
      -(d.c z * longitudinal Δ μ : ℝ) * FlatScalar.firstIntegral Δ μ := by
    rw [firstIntegral_on_unit κ μ unit, firstIntegral_on_unit Δ μ unit,
      show transverse κ μ = _ from transverse_rankOneHessian (d.c z) Δ μ]
    push_cast
    ring
  change boundaryTransport σ Q.val z w = _
  rw [dq,derivative_m d hz w, d.hessian ⟨z, Metric.ball_subset_closedBall hz⟩ w]
  change A*κ-I*γ*Δ - (μ^2*conj (A*κ-I*γ*Δ) + conj Δ*(2*μ*(-I*γ*μ))) =
    -(I*γ + (Real.exp (σ z) * d.c z * longitudinal Δ μ : ℝ)) * FlatScalar.firstIntegral Δ μ
  have ca : conj A = A := Complex.conj_ofReal _
  have cg : conj γ = γ := Complex.conj_ofReal _
  simp only [FlatScalar.firstIntegral] at hess ⊢
  simp only [map_sub, map_mul, Complex.conj_I, ca, cg, Complex.ofReal_mul] at hess ⊢
  change _ = -(I*γ + A * (d.c z) * (longitudinal Δ μ)) * _
  linear_combination A * hess

/-- Construct all transport data of a pencil from the radial Hessian and connection.
Existence of the radial fields, their equations, endpoint incidence, and scalar transport
solvability are separate geometric and analytic questions. -/
def toRaw {σ a} (hs : ContDiff ℝ ∞ σ) (d : Data σ a) : Raw σ a where
  W := d.W
  ρ := d.ρ
  smoothW := d.smoothW
  smoothρ := d.smoothρ
  unitρ := d.unitρ
  zeroW := d.zeroW
  jetW := center_derivative d
  source := source d
  lowerMode := source_extends hs d
  b := b hs d
  derivativeQ := fun _ hz w => derivative_q d hz w
  derivativeM := by
    intro z hz w
    rw [derivative_m d hz w]
    change -I * (connection σ d.k d.W d.ρ z w : ℂ) * (d.ρ z * w) =
      ((Real.exp (σ z) * d.k z / 2 : ℝ) : ℂ) * FlatScalar.firstIntegral (d.W z) (d.ρ z * w)
    rw [firstIntegral_on_unit _ _ (unit_product d hz w)]
    simp only [connection, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_ofNat]
    ring

/-- The endpoint condition uses only alignment of the distance gradient with
the incident velocity, expressed in the same radial parallel frame. -/
def EndpointAlignment {σ} (d : ∀ a : ClosedDisk, Data σ a) : Prop :=
  ∀ z : ClosedDisk, z.val ∈ disk → ∀ w : Circle, ∃ a : ClosedDisk, ‖a.val‖ = 1 ∧
    ∃ s : ℝ, (d a).W z.val = (s : ℂ) * ((d a).ρ z.val * w)

theorem incidence_of_alignment {σ} (hs : ContDiff ℝ ∞ σ) {d : ∀ a : ClosedDisk, Data σ a}
    (ends : EndpointAlignment d) : Incidence (fun a => toRaw hs (d a)) := by
  intro z hz w
  obtain ⟨a, ha, he⟩ := ends z hz w
  exact ⟨a, ha, (firstIntegral_unit_zero_iff_parallel _ _ (unit_product (d a) hz w)).mpr he⟩

/-- The fixed chart Stein properties from scalar transport solvability, the two
covariant field equations, and alignment at the boundary endpoints of geodesics. -/
theorem stein_of_geometry {σ} (hs : ContDiff ℝ ∞ σ) (solve : ScalarSolvability σ)
    (d : ∀ a : ClosedDisk, Data σ a) (ends : EndpointAlignment d) (U : Set ℂ)
    (hU : IsOpen U) (hsub : U ⊆ disk) : HasSteinProperties σ U :=
  stein_of_scalar_and_radial_data solve (fun a => toRaw hs (d a))
    (incidence_of_alignment hs ends) U hU hsub

end TransportOkaGrauert.PencilGeometry
