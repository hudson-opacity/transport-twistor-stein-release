import TransportOkaGrauert.ScalarNormalEnergy
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-! # The base normal operator and its ordinary Lebesgue pairing -/
noncomputable section
namespace TransportOkaGrauert.ScalarRayPairing
open SimpleDiskTarget JacobiEnlargement GeodesicFlowExtension Complex MeasureTheory Set Metric
open scoped ContDiff Topology Interval

private def coords : ScalarLiouville.BoxSpace ≃ᵐ State :=
  ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 2).trans
    ((MeasurableEquiv.refl ℝ).prodCongr Complex.measurableEquivPi.symm)).trans
      MeasurableEquiv.prodComm

private theorem coords_eq (x : ScalarLiouville.BoxSpace) :
    coords x = PolarCollar.direction (ScalarLiouville.point x) := by
  apply Prod.ext
  · change ((x 0 : ℂ) + (x 1 : ℂ)*I) = x 0 • (1:ℂ) + x 1 • I
    simp [Complex.real_smul]
  · rfl

private theorem coords_measure : MeasurePreserving coords := by
  have e₁ := volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 2
  have e₂ := (MeasurePreserving.id (volume : Measure ℝ)).prod Complex.volume_preserving_equiv_pi.symm
  exact Measure.measurePreserving_swap.comp (e₂.comp e₁)

private def planeBox : Set ℂ := {z : ℂ | z.re ∈ Icc (-2:ℝ) 2 ∧ z.im ∈ Icc (-2:ℝ) 2}

private theorem box_eq : coords ⁻¹' (planeBox ×ˢ Icc (-Real.pi) Real.pi) = ScalarLiouville.box := by
  ext x
  rw [mem_preimage,coords_eq]
  change ((x 0 • (1:ℂ) + x 1 • I).re ∈ Icc (-2:ℝ) 2 ∧ (x 0 • (1:ℂ) + x 1 • I).im ∈ Icc (-2:ℝ) 2) ∧
      x 2 ∈ Icc (-Real.pi) Real.pi ↔ ScalarLiouville.lo ≤ x ∧ x ≤ ScalarLiouville.hi
  simp only [add_re,smul_re,one_re,smul_eq_mul,mul_one,I_re,mul_zero,add_zero,add_im,smul_im,one_im,I_im,zero_add]
  constructor
  · rintro ⟨⟨a,b⟩,c⟩
    constructor <;> intro i <;> fin_cases i
    · exact a.1
    · exact b.1
    · exact c.1
    · exact a.2
    · exact b.2
    · exact c.2
  · rintro ⟨a,b⟩
    exact ⟨⟨⟨a 0,b 0⟩,⟨a 1,b 1⟩⟩,⟨a 2,b 2⟩⟩

private theorem plane_compact : IsCompact planeBox := by
  let e := Complex.equivRealProdCLM.symm
  have eq : planeBox = e '' ((Icc (-2:ℝ) 2) ×ˢ (Icc (-2:ℝ) 2)) := by
    ext z
    constructor
    · intro hz; exact ⟨(z.re,z.im),hz,by apply Complex.ext <;> rfl⟩
    · rintro ⟨p,hp,rfl⟩; exact hp
  rw [eq]
  exact (isCompact_Icc.prod isCompact_Icc).image e.continuous

variable {σ : ℂ → ℝ} (F : Flow σ)

/-- Angular integration along one complete fundamental circle, without dividing by `2π`. -/
def angularIntegral (h : AngleTrace) (z : ℂ) := ∫ θ in (-Real.pi)..Real.pi, h (z,θ)

def normal (W : Window F) (f : ℂ → ℝ) := angularIntegral (full F W (fun p => f p.1))

theorem integral_on_base {f : ℂ → ℝ} (hf : Continuous f) (off : ∀ z : ℂ, 1 < ‖z‖ → f z = 0)
    {g : AngleTrace} (hg : Continuous g) :
    integral F (fun p => f p.1 * g p) = ∫ z : ℂ, Real.exp (2*σ z) * f z * angularIntegral g z := by
  let G (p : State) := Real.exp (2*F.factor p.1) * f p.1 * g p
  have cg : Continuous G := ((continuous_const.mul (F.smoothFactor.continuous.comp continuous_fst)).rexp.mul
    (hf.comp continuous_fst)).mul hg
  have eg := coords_measure.setIntegral_preimage_emb coords.measurableEmbedding G
    (planeBox ×ˢ Icc (-Real.pi) Real.pi)
  rw [box_eq] at eg
  have ep : integral F (fun p => f p.1 * g p) = ∫ p in planeBox ×ˢ Icc (-Real.pi) Real.pi, G p := by
    rw [← eg]
    apply setIntegral_congr_fun measurableSet_Icc
    intro x _
    change ScalarLiouville.areaDensity F.factor (ScalarLiouville.point x) * _ = G (coords x)
    rw [coords_eq]
    change Real.exp (2*F.factor (ScalarLiouville.point x).1) * (_ * _) =
      (Real.exp (2*F.factor (ScalarLiouville.point x).1) * _) * _
    ring
  rw [ep,Measure.volume_eq_prod ℂ ℝ,setIntegral_prod G (cg.continuousOn.integrableOn_compact (plane_compact.prod isCompact_Icc))]
  have ang (z : ℂ) : (∫ θ in Icc (-Real.pi) Real.pi, G (z,θ)) =
      Real.exp (2*σ z) * f z * angularIntegral g z := by
    unfold G angularIntegral
    rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),integral_Icc_eq_integral_Ioc]
    change (∫ θ in Ioc (-Real.pi) Real.pi, (Real.exp (2*F.factor z)*f z)*g (z,θ)) = _
    rw [integral_const_mul]
    by_cases h : ‖z‖ ≤ 1
    · rw [(F.germ h).eq_of_nhds]
    · simp [off z (lt_of_not_ge h)]
  simp only [ang]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro z hz
  have no : 1 < ‖z‖ := by
    by_contra! b
    have x := abs_le.mp ((Complex.abs_re_le_norm _).trans b)
    have y := abs_le.mp ((Complex.abs_im_le_norm _).trans b)
    exact hz ⟨⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩⟩
  simp [off z no]

end TransportOkaGrauert.ScalarRayPairing
