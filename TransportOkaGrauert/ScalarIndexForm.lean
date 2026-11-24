import TransportOkaGrauert.ChartJacobi
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # The geodesic index form for a simple conformal disk

Two normalized Jacobi fields, one based at each endpoint, have a sum
strictly positive on the whole segment. Its logarithmic derivative gives a
regular Riccati factorization of the Dirichlet index form, including both
endpoints and with no curvature sign condition.
-/

noncomputable section
namespace TransportOkaGrauert.ScalarIndexForm
open Complex SimpleDiskTarget ChartJacobi Set Metric Filter MeasureTheory
open scoped ContDiff Topology Interval

private theorem reflected {T : ℝ} {f : ℝ → ℝ} {l t : ℝ}
    (df : HasDerivWithinAt f l (Icc 0 T) (T-t)) (_ht : t ∈ Icc 0 T) :
    HasDerivWithinAt (fun s => f (T-s)) (-l) (Icc 0 T) t := by
  have inner : HasDerivWithinAt (fun s : ℝ => T-s) (-1) (Icc 0 T) t :=
    ((hasDerivWithinAt_const t (Icc 0 T) T).sub (hasDerivWithinAt_id t (Icc 0 T))) |>.congr_deriv (by simp)
  simpa [Function.comp_def] using df.scomp t inner (fun s hs => ⟨sub_nonneg.mpr hs.2,sub_le_self _ hs.1⟩)

private theorem reverse_geodesic {σ z θ T} (geo : unitGeodesicOn σ z θ (Icc 0 T)) :
    unitGeodesicOn σ (fun s => z (T-s)) (fun s => θ (T-s)+Real.pi) (Icc 0 T) := by
  intro t ht
  let q := T-t
  have hq : q ∈ Icc 0 T := ⟨sub_nonneg.mpr ht.2,sub_le_self _ ht.1⟩
  have flip (s : ℝ) : (Circle.exp (s+Real.pi) : ℂ) = -(Circle.exp s : ℂ) := by
    rw [Circle.exp_add,Circle.coe_mul]
    have h : (Circle.exp Real.pi : ℂ) = -1 := by simpa only [Circle.coe_exp] using Complex.exp_pi_mul_I
    rw [h,mul_neg_one]
  have ds : HasDerivWithinAt (fun s : ℝ => T-s) (-1) (Icc 0 T) t := by
    simpa using (hasDerivWithinAt_const t (Icc 0 T) T).sub (hasDerivWithinAt_id t (Icc 0 T))
  have maps : MapsTo (fun s => T-s) (Icc 0 T) (Icc 0 T) :=
    fun s hs => ⟨sub_nonneg.mpr hs.2,sub_le_self _ hs.1⟩
  have zv := (geo q hq).1.scomp t ds maps
  have av := ((geo q hq).2.scomp t ds maps).add_const Real.pi
  constructor
  · simpa only [Function.comp_apply,flip,mul_neg,neg_smul,one_smul,q] using zv
  · convert av using 1
    simp only [Isothermal.angularDrift,flip,Complex.neg_re,Complex.neg_im,smul_eq_mul,neg_one_mul,q]
    ring

private theorem normalized {σ z θ T} (simple : SimpleMetric σ) (hT : 0 < T)
    (geo : unitGeodesicOn σ z θ (Icc 0 T))
    (disk : ∀ t ∈ Icc 0 T, z t ∈ closedBall 0 1) :
    ∃ j dj, jacobiOn σ z j dj (Icc 0 T) ∧ j 0 = 0 ∧ ∀ t ∈ Ioc 0 T, 0 < j t := by
  let k : C(Icc 0 T,ℝ) := ⟨fun t => curvature σ (z t), (curvature_contDiff simple.smooth).continuous.comp
    ((show ContinuousOn z (Icc 0 T) from fun t ht => (geo t ht).1.continuousWithinAt).restrict)⟩
  have iv := initial_values hT.le k
  let j := field hT.le k
  let dj := speed hT.le k
  have ode : jacobiOn σ z j dj (Icc 0 T) := solves hT.le k
  refine ⟨j,dj,ode,iv.1,?_⟩
  intro t ht
  have sub : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc_right ht.2
  exact normalized_jacobi_positive simple ht.1
    (fun s hs => ⟨((geo s (sub hs)).1).mono sub,((geo s (sub hs)).2).mono sub⟩)
    (fun s hs => disk s (sub hs))
    (fun s hs => ⟨((ode s (sub hs)).1).mono sub,((ode s (sub hs)).2).mono sub⟩) iv.1 iv.2

/-- Every in-disk geodesic segment admits a Jacobi solution positive even at
the two endpoints. -/
theorem positive_jacobi {σ z θ T} (simple : SimpleMetric σ) (hT : 0 < T)
    (geo : unitGeodesicOn σ z θ (Icc 0 T))
    (disk : ∀ t ∈ Icc 0 T, z t ∈ closedBall 0 1) :
    ∃ j dj, jacobiOn σ z j dj (Icc 0 T) ∧ ∀ t ∈ Icc 0 T, 0 < j t := by
  obtain ⟨f,df,of',f0,pf⟩ := normalized simple hT geo disk
  obtain ⟨g,dg,og,g0,pg⟩ := normalized simple hT (reverse_geodesic geo)
    (fun t ht => disk (T-t) ⟨sub_nonneg.mpr ht.2,sub_le_self _ ht.1⟩)
  refine ⟨fun t => f t + g (T-t),fun t => df t - dg (T-t),?_,?_⟩
  · intro t ht
    have hh := og (T-t) (show T-t ∈ Icc 0 T from ⟨sub_nonneg.mpr ht.2,sub_le_self _ ht.1⟩)
    have o := of' t ht
    refine ⟨by simpa only [sub_eq_add_neg] using o.1.add (reflected hh.1 ht),?_⟩
    convert o.2.sub (reflected hh.2 ht) using 1
    simp only [sub_sub_cancel]; ring
  · intro t ht
    rcases eq_or_lt_of_le ht.1 with h|h
    · simpa [← h,f0] using pg T ⟨hT,le_rfl⟩
    rcases eq_or_lt_of_le ht.2 with e|e
    · simpa [e,g0] using pf T ⟨hT,le_rfl⟩
    exact add_pos (pf t ⟨h,ht.2⟩) (pg _ ⟨sub_pos.mpr e,sub_le_self _ ht.1⟩)

/-- Exact Riccati factorization of the geodesic index form on all real
Dirichlet test functions with continuous first derivative. -/
theorem index_factorization {σ z θ T} (simple : SimpleMetric σ) (hT : 0 < T)
    (geo : unitGeodesicOn σ z θ (Icc 0 T))
    (disk : ∀ t ∈ Icc 0 T, z t ∈ closedBall 0 1) :
    ∃ r : ℝ → ℝ, ContinuousOn r (Icc 0 T) ∧
      (∀ t ∈ Icc 0 T, HasDerivWithinAt r (-curvature σ (z t) - r t ^ 2) (Icc 0 T) t) ∧
      ∀ u du : ℝ → ℝ, (∀ t ∈ Icc 0 T, HasDerivWithinAt u (du t) (Icc 0 T) t) →
        ContinuousOn du (Icc 0 T) → u 0 = 0 → u T = 0 →
        (∫ t in 0..T, du t ^ 2 - curvature σ (z t) * u t ^ 2) =
          ∫ t in 0..T, (du t - r t * u t)^2 := by
  obtain ⟨j,dj,ode,positive⟩ := positive_jacobi simple hT geo disk
  let r := fun t => dj t / j t
  have dr (t : ℝ) (ht : t ∈ Icc 0 T) : HasDerivWithinAt r (-curvature σ (z t) - r t^2) (Icc 0 T) t := by
    have hh := ode t ht
    convert hh.2.div hh.1 (positive t ht).ne' using 1
    dsimp only [r]
    field_simp [(positive t ht).ne']
  have cr : ContinuousOn r (Icc 0 T) := fun t ht => (dr t ht).continuousWithinAt
  refine ⟨r,cr,dr,?_⟩
  intro u du hu cu' u0 uT
  have cu : ContinuousOn u (Icc 0 T) := fun t ht => (hu t ht).continuousWithinAt
  let k := fun t => curvature σ (z t)
  have ck : ContinuousOn k (Icc 0 T) := (curvature_contDiff simple.smooth).continuous.comp_continuousOn
    (fun t ht => (geo t ht).1.continuousWithinAt)
  let A (t : ℝ) := du t ^ 2 - k t * u t ^ 2
  let B (t : ℝ) := (du t-r t*u t)^2
  have ca : ContinuousOn A (Icc 0 T) := (cu'.pow 2).sub (ck.mul (cu.pow 2))
  have cb : ContinuousOn B (Icc 0 T) := (cu'.sub (cr.mul cu)).pow 2
  have d (t : ℝ) (ht : t ∈ Icc 0 T) : HasDerivWithinAt (fun s => r s * u s ^ 2)
      (A t - B t) (Icc 0 T) t := by
    convert (dr t ht).mul ((hu t ht).pow 2) using 1
    dsimp [A,B,k]
    ring
  have int {g : ℝ → ℝ} (c : ContinuousOn g (Icc 0 T)) : IntervalIntegrable g volume 0 T :=
    (uIcc_of_le hT.le ▸ c).intervalIntegrable
  have eq := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT.le (cr.mul (cu.pow 2))
    (fun t ht => (d t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)) (int (ca.sub cb))
  rw [intervalIntegral.integral_sub (int ca) (int cb)] at eq
  simp only [Pi.mul_apply,u0,uT,zero_pow (by decide : 2 ≠ 0),mul_zero,sub_zero] at eq
  simpa [A,B,k] using (sub_eq_zero.mp (by simpa using eq : (∫ t in 0..T, A t) - (∫ t in 0..T, B t) = 0))

/-- The Dirichlet index form on each in-disk geodesic segment of a simple
metric has a strictly positive lower bound in the squared `L²` norm. -/
theorem index_coercive {σ z θ T} (simple : SimpleMetric σ) (hT : 0 < T)
    (geo : unitGeodesicOn σ z θ (Icc 0 T))
    (disk : ∀ t ∈ Icc 0 T, z t ∈ closedBall 0 1) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ u du : ℝ → ℝ,
      (∀ t ∈ Icc 0 T, HasDerivWithinAt u (du t) (Icc 0 T) t) →
      ContinuousOn du (Icc 0 T) → u 0 = 0 → u T = 0 →
      ε * (∫ t in 0..T, u t ^ 2) ≤ ∫ t in 0..T, du t ^ 2 - curvature σ (z t) * u t ^ 2 := by
  obtain ⟨r,cr,dr,_⟩ := index_factorization simple hT geo disk
  obtain ⟨M,bound⟩ := isCompact_Icc.bddAbove_image cr.abs
  have mb (t : ℝ) (ht : t ∈ Icc 0 T) : |r t| ≤ M := bound ⟨t,ht,rfl⟩
  have m0 : 0 ≤ M := (abs_nonneg _).trans (mb 0 ⟨le_rfl,hT.le⟩)
  let A := 2*M+2
  have ap : 0 < A := by dsimp [A]; linarith
  let s := fun t : ℝ => Real.exp (A*(t-T))
  let ε := s 0
  have s1 (t : ℝ) (ht : t ∈ Icc 0 T) : s t ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos ap.le (sub_nonpos.mpr ht.2))
  have se (t : ℝ) (ht : t ∈ Icc 0 T) : ε ≤ s t :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith [ht.1]) ap.le)
  have ds (t : ℝ) : HasDerivAt s (A*s t) t := by
    convert (((hasDerivAt_id t).sub_const T).const_mul A).exp using 1 <;> simp [s,mul_comm]
  let R := fun t => r t-s t
  let k := fun t => curvature σ (z t)
  let dR := fun t => -k t - r t^2 - A*s t
  have dR' (t : ℝ) (ht : t ∈ Icc 0 T) : HasDerivWithinAt R (dR t) (Icc 0 T) t :=
    (dr t ht).sub (ds t).hasDerivWithinAt
  have residual (t : ℝ) (ht : t ∈ Icc 0 T) : dR t + R t ^ 2 + k t ≤ -ε := by
    have h : 1 ≤ A + 2*r t - s t := by
      dsimp only [A]; linarith [(abs_le.mp (mb t ht)).1,s1 t ht]
    have b := mul_le_mul_of_nonneg_left h (Real.exp_pos (A*(t-T))).le
    change s t * 1 ≤ s t * _ at b
    dsimp only [dR,R]
    nlinarith [se t ht]
  refine ⟨ε,Real.exp_pos _,?_⟩
  intro u du hu cu' u0 uT
  have cu : ContinuousOn u (Icc 0 T) := fun t ht => (hu t ht).continuousWithinAt
  have ck : ContinuousOn k (Icc 0 T) := (curvature_contDiff simple.smooth).continuous.comp_continuousOn
    (fun t ht => (geo t ht).1.continuousWithinAt)
  have cs : Continuous s := continuous_iff_continuousAt.mpr (fun t => (ds t).continuousAt)
  have cR : ContinuousOn R (Icc 0 T) := cr.sub cs.continuousOn
  have cdR : ContinuousOn dR (Icc 0 T) := (ck.neg.sub (cr.pow 2)).sub (continuousOn_const.mul cs.continuousOn)
  let D := fun t => dR t*u t^2 + R t*(2*u t*du t)
  have d (t : ℝ) (ht : t ∈ Icc 0 T) : HasDerivWithinAt (fun t => R t*u t^2) (D t) (Icc 0 T) t := by
    convert (dR' t ht).mul ((hu t ht).pow 2) using 1
    dsimp [D]; ring
  have cD : ContinuousOn D (Icc 0 T) := (cdR.mul (cu.pow 2)).add (cR.mul ((continuousOn_const.mul cu).mul cu'))
  have int {g : ℝ → ℝ} (c : ContinuousOn g (Icc 0 T)) : IntervalIntegrable g volume 0 T :=
    (uIcc_of_le hT.le ▸ c).intervalIntegrable
  have eq := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT.le (cR.mul (cu.pow 2))
    (fun t ht => (d t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)) (int cD)
  simp only [Pi.mul_apply,u0,uT,zero_pow (by decide : 2 ≠ 0),mul_zero,sub_zero] at eq
  let E := fun t => du t^2 - k t*u t^2
  have cE : ContinuousOn E (Icc 0 T) := (cu'.pow 2).sub (ck.mul (cu.pow 2))
  have pt (t : ℝ) (ht : t ∈ Icc 0 T) : ε * u t^2 ≤ E t - D t := by
    have b := mul_le_mul_of_nonneg_right (residual t ht) (sq_nonneg (u t))
    dsimp only [E,D]
    nlinarith [sq_nonneg (du t - R t*u t)]
  have result := intervalIntegral.integral_mono_on hT.le (int (continuousOn_const.mul (cu.pow 2)))
    (int (cE.sub cD)) pt
  change (∫ t in 0..T, ε * u t^2) ≤ ∫ t in 0..T, E t - D t at result
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_sub (int cE) (int cD), eq, sub_zero] at result
  exact result

end TransportOkaGrauert.ScalarIndexForm
