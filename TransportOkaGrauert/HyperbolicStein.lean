import TransportOkaGrauert.HyperbolicPencil
import TransportOkaGrauert.HyperbolicDisk
import TransportOkaGrauert.ChartHolAlgebra

/-! # The three Stein axioms for a Poincaré metric on every open subdomain
of the base disk. The scalar right inverse and radial pencils for an arbitrary
simple metric are not required in this model. -/
namespace TransportOkaGrauert.HyperbolicStein
noncomputable section
open Set Complex Metric ChartStein HyperbolicCR
open scoped ContDiff ComplexConjugate

private theorem scaled_lt {c : ℝ} (hc : 0 < c) (hc' : c < 1) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖(c:ℂ)*z‖ < 1 := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
  exact (mul_le_mul_of_nonneg_left hz hc.le).trans_lt (by simpa using hc')

private theorem end_cont {c ε : ℝ} (hc : 0 < c) (h1 : c < 1) (hε : ε=1 ∨ ε= -1) :
    Continuous ((endpoint c ε) ∘ point) := by
  let s (p : CompactBundle) := (c:ℂ)*p.1.val
  let w (p : CompactBundle) := (ε:ℂ)*p.2.val
  have hs : Continuous s := continuous_const.mul (continuous_subtype_val.comp continuous_fst)
  have hw : Continuous w := continuous_const.mul (continuous_subtype_val.comp continuous_snd)
  have dn (p : CompactBundle) : 1+conj (s p)*w p ≠ 0 := by
    apply HyperbolicDisk.nonzero (scaled_lt hc h1 (mem_closedBall_zero_iff.mp p.1.property))
    have hh := mem_closedBall_zero_iff.mp p.2.property
    rcases hε with rfl | rfl <;> simpa [w] using hh
  simpa only [Function.comp_def, endpoint, point, s, w, mul_assoc] using
    (hs.add hw).div (continuous_const.add ((Complex.continuous_conj.comp hs).mul hw)) dn

private theorem pencil_cont {c : ℝ} (hc : 0<c) (h1 : c<1) (a : ℂ) :
    Continuous ((HyperbolicPencil.divisor c a) ∘ point) := by
  have A := end_cont (ε := 1) hc h1 (Or.inl rfl)
  have B := end_cont (ε := -1) hc h1 (Or.inr rfl)
  exact ((A.sub continuous_const).mul (continuous_const.sub (continuous_const.mul B))).add
    ((B.sub continuous_const).mul (continuous_const.sub (continuous_const.mul A)))

private theorem pencil_hol {c : ℝ} (hc : 0<c) (h1 : c<1) (a : ℂ) {p : E}
    (hz : ‖p.1‖<1) (hw : ‖p.2‖<1) : HolAt (factor c) (HyperbolicPencil.divisor c a) p := by
  have A := endpoint_hol (ε := 1) hc h1 (Or.inl rfl) hz hw
  have B := endpoint_hol (ε := -1) hc h1 (Or.inr rfl) hz hw
  let C := holAt_const (factor c) p
  exact ((A.sub (C _)).mul ((C 1).sub ((C _).mul B))).add
    ((B.sub (C _)).mul ((C 1).sub ((C _).mul A)))

private theorem endpoint_eq (c : ℝ) (p : E) :
    endpoint c 1 p = HyperbolicDisk.mob ((c:ℂ)*p.1) p.2 := by
  simp [endpoint,HyperbolicDisk.mob]

/-- Unconditional curved family. The restriction excludes the degeneracy at
the ideal boundary when c=1. The base subdomain need not have regular boundary. -/
theorem poincare_disk {c : ℝ} (hc : 0<c) (h1 : c<1)
    (U : Set ℂ) (_hU : IsOpen U) (hsub : U ⊆ ball 0 1) : HasSteinProperties (factor c) U := by
  let A := endpoint c 1
  let F := HyperbolicPencil.divisor c
  have inside (p : interiorOver U) := mem_ball_zero_iff.mp (hsub p.property.1)
  have holA : HolOn (factor c) U A :=
    fun p => endpoint_hol hc h1 (Or.inl rfl) (inside p) p.property.2
  have holF (a : ℂ) : HolOn (factor c) U (F a) :=
    fun p => pencil_hol hc h1 a (inside p) p.property.2
  have closedBound (x : ClosedDisk) : ‖x.val‖ ≤ 1 := mem_closedBall_zero_iff.mp x.property
  constructor
  · intro K hK
    letI : CompactSpace ClosedDisk := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
    apply DivisorHull.isCompact_testHull_of_boundary_divisors (fun _ h => continuous_tests h) _ hK
    intro p hout
    suffices witness : ∃ f : E → ℂ, Continuous (f ∘ point) ∧ HolOn (factor c) U f ∧
        f (point p) = 0 ∧ ∀ u : interiorOver U, f (point u.val) ≠ 0 by
      obtain ⟨f,hcont,hhol,hp,hn⟩ := witness
      exact ⟨f ∘ point,hcont,hp,hn,fun q => (f q)⁻¹,fun u => (hhol u).inv (hn u),fun _ => rfl⟩
    by_cases hb : p.1.val ∈ U
    · have hw : ‖p.2.val‖ = 1 := le_antisymm (closedBound _) (le_of_not_gt (fun h => hout ⟨hb,h⟩))
      have hr : ‖A (point p)‖ = 1 := by
        rw [show A (point p) = _ from endpoint_eq c _]
        exact HyperbolicDisk.norm_eq (scaled_lt hc h1 (closedBound _)) hw
      refine ⟨fun q => A q-A (point p), (end_cont hc h1 (Or.inl rfl)).sub continuous_const,
        fun u => (holA u).sub (holAt_const _ _ _),sub_self _,?_⟩
      intro u eq
      have hu : ‖A (point u.val)‖ < 1 := by
        rw [show A (point u.val) = _ from endpoint_eq c _]
        exact HyperbolicDisk.norm_lt (scaled_lt hc h1 (closedBound _)) u.property.2
      exact (ne_of_lt hu) ((congrArg norm (sub_eq_zero.mp eq)).trans hr)
    · refine ⟨F p.1.val,pencil_cont hc h1 _,holF _,HyperbolicPencil.at_centre hc h1
          (closedBound _) (closedBound _),?_⟩
      intro u h
      exact hb ((HyperbolicPencil.zero_iff hc h1 (closedBound _) (closedBound _) u.property.2).mp h ▸
        u.property.1)
  · intro p q hne
    by_cases hb : p.val.1.val=q.val.1.val
    · refine ⟨A,holA,?_⟩
      intro h
      change endpoint c 1 _ = endpoint c 1 _ at h
      simp only [endpoint_eq,point,hb] at h
      exact hne (Subtype.ext (Prod.ext (Subtype.ext hb) (Subtype.ext
        (HyperbolicDisk.injective_on_disk (scaled_lt hc h1 (closedBound _))
          p.property.2.le q.property.2.le h))))
    · refine ⟨F p.val.1.val,holF _,?_⟩
      intro eq
      have hp : F p.val.1.val (point p.val) = 0 :=
        HyperbolicPencil.at_centre hc h1 (closedBound _) (closedBound _)
      exact hb ((HyperbolicPencil.zero_iff hc h1 (closedBound _) (closedBound _) q.property.2).mp (eq.symm.trans hp)).symm
  · intro p
    exact ⟨F p.val.1.val,A,holF _,holA,HyperbolicPencil.coordinates hc h1
      (closedBound _) p.property.2⟩
end
end TransportOkaGrauert.HyperbolicStein
