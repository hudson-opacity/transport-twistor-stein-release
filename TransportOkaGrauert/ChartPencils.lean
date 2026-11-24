import TransportOkaGrauert.GeodesicEndpoint
import TransportOkaGrauert.PencilCoordinates
import TransportOkaGrauert.PencilLifts

/-! # From scalar transport and radial geometry to the three chart Stein properties -/
namespace TransportOkaGrauert.ChartPencils
noncomputable section
open Set Complex Metric ChartStein ChartCorrespondence PencilLifts
open scoped ContDiff ComplexConjugate

/-- The velocity coordinate in a moving orthonormal frame. -/
def moving (ρ : ℂ → ℂ) (hρ : ContDiff ℝ ∞ ρ) : DiskFunction where
  val x := ρ x.1 * x.2
  smooth := (hρ.comp contDiff_fst).mul contDiff_snd
  fibre z _ := (differentiableOn_const (c := ρ z)).mul differentiableOn_id

/-- The radial pencil before either scalar transport correction. -/
def radial (W ρ : ℂ → ℂ) (hW : ContDiff ℝ ∞ W) (hρ : ContDiff ℝ ∞ ρ) : DiskFunction where
  val x := FlatScalar.firstIntegral (W x.1) ((moving ρ hρ).val x)
  smooth := (hW.comp contDiff_fst).sub (((moving ρ hρ).smooth.pow 2).mul
    (Complex.conjCLE.contDiff.comp (hW.comp contDiff_fst)))
  fibre z _ := ((SteinDivisor.firstIntegral_fibre_holomorphic (W z)).comp
    ((differentiable_const (ρ z)).mul differentiable_id)).differentiableOn

/-- Geometric and transport input for a pencil centered at a. All equations
involve explicitly specified polynomials and the real geodesic derivative. -/
structure Raw (σ : ℂ → ℝ) (a : ClosedDisk) where
  W : ℂ → ℂ
  ρ : ℂ → ℂ
  smoothW : ContDiff ℝ ∞ W
  smoothρ : ContDiff ℝ ∞ ρ
  unitρ : ∀ z : ClosedDisk, ‖ρ z.val‖ = 1
  zeroW : ∀ z : ClosedDisk, W z.val = 0 ↔ z = a
  jetW : Function.Injective (fderiv ℝ W a.val)
  source : TraceRHS
  lowerMode : ShiftExtends source
  b : DiskFunction
  derivativeQ : ∀ z ∈ disk, ∀ w : Circle,
    boundaryTransport σ (radial W ρ smoothW smoothρ).val z w =
      -source z w * (radial W ρ smoothW smoothρ).val (z,w)
  derivativeM : ∀ z ∈ disk, ∀ w : Circle,
    boundaryTransport σ (moving ρ smoothρ).val z w =
      b.val (z,w) * (radial W ρ smoothW smoothρ).val (z,w)

abbrev Raw.q {σ a} (d : Raw σ a) := radial d.W d.ρ d.smoothW d.smoothρ
abbrev Raw.m {σ a} (d : Raw σ a) := moving d.ρ d.smoothρ

/-- A boundary-base centre has a pencil through each unit direction above
an interior base point. This is the incidence property of a geodesic endpoint. -/
def Incidence {σ} (d : ∀ a : ClosedDisk, Raw σ a) : Prop :=
  ∀ (z : ClosedDisk), z.val ∈ disk → ∀ w : Circle, ∃ a : ClosedDisk,
    ‖a.val‖ = 1 ∧ (d a).q.val (z.val,w) = 0

/-- The raw data and a scalar right inverse suffice for hulls, separation,
and coordinates on every open base subdomain, including the entire disk. -/
theorem stein_of_scalar_and_radial_data {σ : ℂ → ℝ} (solve : ScalarSolvability σ)
    (d : ∀ a : ClosedDisk, Raw σ a) (inc : Incidence d)
    (U : Set ℂ) (_hU : IsOpen U) (hsub : U ⊆ disk) : HasSteinProperties σ U := by
  classical
  have lifts (a : ClosedDisk) := correct_pencil solve (d a).q (d a).m (d a).b
    (d a).source (d a).lowerMode (d a).derivativeQ (d a).derivativeM
  choose l u hF hG using lifts
  let F (a : ClosedDisk) := (l a).exp.mul (d a).q
  let G (a : ClosedDisk) := (d a).m.sub ((u a).mul (F a))
  have restr {f : E → ℂ} (h : HolOn σ disk f) : HolOn σ U f :=
    fun p => h ⟨p.val, hsub p.property.1, p.property.2⟩
  have zeroF (a z v : ClosedDisk) (hv : ‖v.val‖ < 1) :
      (F a).val (z.val,v.val) = 0 ↔ z = a := by
    have hm : ‖(d a).ρ z.val * v.val‖ < 1 := by simpa [(d a).unitρ z] using hv
    exact (SteinDivisor.corrected_interior_zero_iff _ _ _ (Complex.exp_ne_zero _) hm).trans
      ((d a).zeroW z)
  have centre (a v : ClosedDisk) : (F a).val (a.val,v.val) = 0 := by
    change Complex.exp _ * FlatScalar.firstIntegral ((d a).W a.val) _ = 0
    simp [((d a).zeroW a).mpr rfl, FlatScalar.firstIntegral]
  have interp (a v : ClosedDisk) : (G a).val (a.val,v.val) = (d a).ρ a.val * v.val := by
    change _ - _ * (F a).val (a.val,v.val) = _
    rw [centre, mul_zero, sub_zero]
    rfl
  constructor
  · intro K hK
    letI : CompactSpace ClosedDisk := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
    apply DivisorHull.isCompact_testHull_of_boundary_divisors
      (fun _ h => continuous_tests h) _ hK
    intro p hout
    suffices witness : ∃ a : ClosedDisk, a.val ∉ U ∧ (F a).val (point p) = 0 by
      obtain ⟨a,ha,hp⟩ := witness
      have nz (v : interiorOver U) : (F a).val (point v.val) ≠ 0 := by
        intro he
        have eq := (zeroF a _ _ v.property.2).mp he
        exact ha (eq ▸ v.property.1)
      exact ⟨(F a).val ∘ point, (F a).smooth.continuous.comp continuous_point, hp, nz,
        fun q => ((F a).val q)⁻¹, fun v => (restr (hF a) v).inv (nz v), fun _ => rfl⟩
    by_cases hb : p.1.val ∈ U
    · have hw : ‖p.2.val‖ = 1 := le_antisymm (mem_closedBall_zero_iff.mp p.2.property)
          (le_of_not_gt (fun hh => hout ⟨hb, hh⟩))
      let w : Circle := ⟨p.2.val, mem_sphere_zero_iff_norm.mpr hw⟩
      obtain ⟨a, ha, hq⟩ := inc p.1 (hsub hb) w
      refine ⟨a, fun h => ?_, ?_⟩
      · have hh := mem_ball_zero_iff.mp (hsub h)
        linarith
      · change Complex.exp _ * (d a).q.val (p.1.val,(w:ℂ)) = 0
        rw [hq, mul_zero]
    · exact ⟨p.1,hb,centre p.1 p.2⟩
  · intro p r hne
    let a := p.val.1
    by_cases hbase : r.val.1 = a
    · refine ⟨(G a).val, restr (hG a), ?_⟩
      intro he
      change (G a).val (a.val,p.val.2.val) = (G a).val (r.val.1.val,r.val.2.val) at he
      rw [hbase, interp, interp] at he
      have hn : (d a).ρ a.val ≠ 0 := by
        intro h
        have hr := (d a).unitρ a
        simp [h] at hr
      exact hne (Subtype.ext (Prod.ext hbase.symm (Subtype.ext (mul_left_cancel₀ hn he))))
    · refine ⟨(F a).val, restr (hF a), ?_⟩
      intro he
      exact hbase ((zeroF a _ _ r.property.2).mp (he ▸ centre a p.val.2))
  · intro p
    let a := p.val.1
    refine ⟨(F a).val,(G a).val,restr (hF a),restr (hG a), ?_⟩
    exact PencilCoordinates.at_center ((d a).smoothW.differentiable (by simp) _)
      ((d a).smoothρ.differentiable (by simp) _) ((l a).smooth.differentiable (by simp) _)
      ((u a).smooth.differentiable (by simp) _) (((d a).zeroW a).mpr rfl)
      (d a).jetW ((d a).unitρ a) p.property.2

/-- Recover radial incidence from the given nontrapping condition by following
a conserved pencil to its first intersection with the base circle. -/
theorem incidence_of_simplicity {σ : ℂ → ℝ} (simple : SimpleDiskTarget.SimpleMetric σ)
    (solve : ScalarSolvability σ) (d : ∀ a : ClosedDisk, Raw σ a) : Incidence d := by
  classical
  have lifts (a : ClosedDisk) := correct_pencil_with_trace solve (d a).q (d a).m (d a).b
    (d a).source (d a).lowerMode (d a).derivativeQ (d a).derivativeM
  choose l u hF hG conserved using lifts
  let F (a : ClosedDisk) := (l a).exp.mul (d a).q
  have centre (a : ClosedDisk) (w : Circle) : (F a).val (a.val,w) = 0 := by
    change Complex.exp _ * FlatScalar.firstIntegral ((d a).W a.val) _ = 0
    simp [((d a).zeroW a).mpr rfl, FlatScalar.firstIntegral]
  intro z hz w
  obtain ⟨a,ha,h⟩ := GeodesicEndpoint.detector simple (fun a => (F a).val)
    (fun a => (F a).smooth) conserved centre z hz w
  exact ⟨a,ha,(mul_eq_zero.mp h).resolve_left (Complex.exp_ne_zero _)⟩

theorem stein_for_simple_disk {σ : ℂ → ℝ} (simple : SimpleDiskTarget.SimpleMetric σ)
    (solve : ScalarSolvability σ) (d : ∀ a : ClosedDisk, Raw σ a)
    (U : Set ℂ) (hU : IsOpen U) (hsub : U ⊆ disk) : HasSteinProperties σ U :=
  stein_of_scalar_and_radial_data solve d (incidence_of_simplicity simple solve d) U hU hsub

end
end TransportOkaGrauert.ChartPencils
