import TransportOkaGrauert.SimpleRadialExit
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Analysis.Convex.Star

/-! # The first-exit star of an endpoint map

The retained velocities are exactly those whose full radial segment stays in
the closed disk. Escape in every direction makes this set compact. The open
star, defined by strict inequalities on the entire segment, is open and
star-convex without any regularity hypothesis on the exit time.
-/

noncomputable section
namespace TransportOkaGrauert.SimpleRadialStar

open Set Metric Complex Filter SimpleDiskTarget SimpleRadialExit
open scoped Topology

def retained (f : ℂ → ℂ) (R : ℝ) : Set ℂ :=
  {x | ∀ t ∈ Icc (0 : ℝ) 1, ‖f (t • x)‖ ≤ R}

def beforeExit (f : ℂ → ℂ) (R : ℝ) : Set ℂ :=
  {x | ∀ t ∈ Icc (0 : ℝ) 1, ‖f (t • x)‖ < R}

theorem isClosed_retained {f : ℂ → ℂ} (hf : Continuous f) (R : ℝ) :
    IsClosed (retained f R) := by
  have eq : retained f R = ⋂ t : Icc (0 : ℝ) 1, {x : ℂ | ‖f (t.val • x)‖ ≤ R} := by
    ext x
    simp [retained]
  rw [eq]
  exact isClosed_iInter (fun t => isClosed_le ((hf.comp (continuous_const.smul continuous_id)).norm) continuous_const)

/-- Pointwise escape, even with discontinuously selected escape times,
bounds all retained initial velocities uniformly. -/
theorem isCompact_retained {f : ℂ → ℂ} (hf : Continuous f) {R : ℝ}
    (escapes : ∀ w : Circle, ∃ t : ℝ, 0 < t ∧ R < ‖f (t • (w : ℂ))‖) :
    IsCompact (retained f R) := by
  classical
  choose T pos outside using escapes
  let O (w : Circle) := {v : Circle | R < ‖f (T w • (v : ℂ))‖}
  have op (w : Circle) : IsOpen (O w) := isOpen_lt continuous_const
    (hf.comp (continuous_const.smul continuous_subtype_val)).norm
  have cover : (univ : Set Circle) ⊆ ⋃ w, O w := fun w _ => mem_iUnion.mpr ⟨w, outside w⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover O op cover
  let M : ℝ := ∑ i ∈ s, T i
  have bound (i : Circle) (hi : i ∈ s) : T i ≤ M :=
    Finset.single_le_sum (f := T) (fun j _ => (pos j).le) hi
  have nonneg : 0 ≤ M := Finset.sum_nonneg (fun j _ => (pos j).le)
  apply (isCompact_closedBall (0 : ℂ) M).of_isClosed_subset (isClosed_retained hf R)
  intro x hx
  apply mem_closedBall_zero_iff.mpr
  by_contra! hm
  have hp : 0 < ‖x‖ := nonneg.trans_lt hm
  let w : Circle := ⟨‖x‖⁻¹ • x, mem_sphere_zero_iff_norm.mpr (by
    simp [hp.ne'])⟩
  obtain ⟨i, hi, hit⟩ := mem_iUnion₂.mp (hs (mem_univ w))
  have sub : T i / ‖x‖ ∈ Icc (0 : ℝ) 1 :=
    ⟨(div_pos (pos i) hp).le, (div_le_one hp).mpr ((bound i hi).trans hm.le)⟩
  have stop := hx (T i / ‖x‖) sub
  change R < ‖f (T i • (‖x‖⁻¹ • x))‖ at hit
  rw [smul_smul, ← div_eq_mul_inv] at hit
  exact (not_lt_of_ge stop) hit

theorem isOpen_beforeExit {f : ℂ → ℂ} (hf : Continuous f) (R : ℝ) :
    IsOpen (beforeExit f R) := by
  let bad := {p : ℂ × Icc (0 : ℝ) 1 | R ≤ ‖f (p.2.val • p.1)‖}
  have hclosed : IsClosed bad :=
    isClosed_le continuous_const (hf.comp ((continuous_subtype_val.comp continuous_snd).smul continuous_fst)).norm
  have eq : beforeExit f R = (Prod.fst '' bad)ᶜ := by
    ext x
    simp [beforeExit, bad]
  rw [eq]
  exact (isClosedMap_fst_of_compactSpace bad hclosed).isOpen_compl

theorem starConvex_beforeExit (f : ℂ → ℂ) (R : ℝ) :
    StarConvex ℝ 0 (beforeExit f R) := by
  intro x hx a b ha hb hab t ht
  simp only [smul_zero, zero_add, smul_smul]
  exact hx (t*b) ⟨mul_nonneg ht.1 hb, mul_le_one₀ ht.2 hb (by linarith)⟩

/-- A ray lying in the closed disk cannot touch the boundary at an intermediate
time when it starts strictly inside. Its first boundary hit would be transverse,
and squared radius would strictly increase past one. -/
theorem no_interior_contact {σ z θ b} (simple : SimpleMetric σ)
    (ray : unitGeodesicOn σ z θ (Icc 0 b)) (h0 : ‖z 0‖ < 1)
    (closed : ∀ t ∈ Icc 0 b, ‖z t‖ ≤ 1) :
    ∀ t ∈ Ico 0 b, ‖z t‖ < 1 := by
  intro t ht
  by_contra! hbad
  have cz : ContinuousOn z (Icc 0 t) :=
    fun s hs => ((ray s ((Icc_subset_Icc_right ht.2.le) hs)).1.continuousWithinAt).mono
      (Icc_subset_Icc_right ht.2.le)
  obtain ⟨u,hu,bd,inside⟩ := GeodesicEndpoint.first_exit ht.1 cz h0 hbad
  have hp : 0 < u := lt_of_le_of_ne hu.1 (by rintro rfl; linarith)
  have hb' : u < b := hu.2.trans_lt ht.2
  have hlt := transverse_hit simple ray (by norm_num : (0 : ℝ) ≤ 0) hp hb' bd inside
  have hd := radiusSq_deriv ray (Icc_mem_nhds hp hb')
  have hs := (hasDerivAt_iff_tendsto_slope_left_right.mp hd).2.eventually
    (Ioi_mem_nhds (mul_pos (mul_pos (by norm_num) (Real.exp_pos _)) hlt))
  obtain ⟨v, huv, hsub⟩ := (mem_nhdsGT_iff_exists_mem_Ioc_Ioo_subset hb').mp hs
  obtain ⟨r, hru, hrv⟩ := exists_between huv.1
  have h := hsub (show r ∈ Ioo u v from ⟨hru, hrv⟩)
  change 0 < slope (fun s => normSq (z s)) u r at h
  rw [slope_def_field] at h
  have hi := (div_pos_iff_of_pos_right (sub_pos.mpr hru)).mp h
  have he := closed r ⟨(hp.trans hru).le, hrv.le.trans huv.2⟩
  simp only [normSq_eq_norm_sq, bd, one_pow] at hi
  nlinarith [norm_nonneg (z r)]

/-- Arclength along the ray with initial velocity direction `x/‖x‖`. -/
def along (f : ℂ → ℂ) (x : ℂ) (t : ℝ) : ℂ := f ((t/‖x‖) • x)

theorem along_scaled (f : ℂ → ℂ) {x : ℂ} (hx : x ≠ 0) (t : ℝ) :
    along f x (t * ‖x‖) = f (t • x) := by
  simp [along, norm_ne_zero_iff.mpr hx]

theorem along_retained {f : ℂ → ℂ} {x : ℂ} (hx : x ≠ 0) (h : x ∈ retained f 1) :
    ∀ t ∈ Icc (0 : ℝ) ‖x‖, along f x t ∈ closedBall (0 : ℂ) 1 := by
  intro t ht
  have hp := norm_pos_iff.mpr hx
  exact mem_closedBall_zero_iff.mpr (h _ ⟨div_nonneg ht.1 hp.le, (div_le_one hp).mpr ht.2⟩)

/-- The preimage of the open target in the compact retained star is exactly
the open star. Strict boundary convexity excludes a premature tangent contact. -/
theorem retained_inter_preimage {f : ℂ → ℂ} {σ : ℂ → ℝ} (simple : SimpleMetric σ)
    (h0 : ‖f 0‖ < 1)
    (rays : ∀ x ∈ retained f 1, x ≠ 0 → ∃ θ, unitGeodesicOn σ (along f x) θ (Icc 0 ‖x‖)) :
    retained f 1 ∩ f ⁻¹' ball (0 : ℂ) 1 = beforeExit f 1 := by
  ext x
  constructor
  · rintro ⟨hx, htarget⟩ t ht
    by_cases hx0 : x = 0
    · simpa [hx0] using h0
    rcases lt_or_eq_of_le ht.2 with h | he
    · obtain ⟨θ, ray⟩ := rays x hx hx0
      have hp := norm_pos_iff.mpr hx0
      have hit := no_interior_contact simple ray (by simpa [along] using h0)
        (fun u hu => mem_closedBall_zero_iff.mp (along_retained hx0 hx u hu))
        (t * ‖x‖) ⟨mul_nonneg ht.1 hp.le, by simpa using mul_lt_mul_of_pos_right h hp⟩
      simpa [along_scaled f hx0] using hit
    · simpa [he] using mem_ball_zero_iff.mp htarget
  · intro h
    exact ⟨fun t ht => (h t ht).le, mem_ball_zero_iff.mpr (by
      simpa using h 1 (right_mem_Icc.mpr zero_le_one))⟩

end TransportOkaGrauert.SimpleRadialStar
