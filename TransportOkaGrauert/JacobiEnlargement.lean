import TransportOkaGrauert.GeodesicNonreturn
import TransportOkaGrauert.GlobalGeodesicFlow
import TransportOkaGrauert.ScalarGeneralUnrestricted
import TransportOkaGrauert.ChartJacobi
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Stability of the normal Jacobi determinant on larger geodesic disks

At a zero-length segment the quotient of the normalized Jacobi field by
elapsed time has value one. Its integral representation gives continuity,
so that compactness controls short segments along with all other segments.
-/

noncomputable section
namespace TransportOkaGrauert.JacobiEnlargement

open Complex SimpleDiskTarget ChartJacobi GeodesicFlowExtension GeodesicNonreturn
open PathContinuation Set Metric Filter MeasureTheory
open scoped ContDiff Topology Interval NNReal

structure Flow (σ : ℂ → ℝ) where
  factor : ℂ → ℝ
  smoothFactor : ContDiff ℝ ∞ factor
  agrees : ∃ e > (0:ℝ), ∀ z : ℂ, normSq z < 1+e → factor z = σ z
  convex : ∀ z : ℂ, 1 ≤ ‖z‖ → 0 < 1 + fderiv ℝ factor z z
  val : State × ℝ → State
  smooth : ContDiff ℝ ∞ val
  initial : ∀ p, val (p,0) = p
  ode : ∀ p t, HasDerivAt (fun s => val (p,s)) (chartVector factor (val (p,t))) t
  group : ∀ p t s, val (val (p,t),s) = val (p,t+s)
  periodic : ∀ p a, Circle.exp a = 1 → ∀ t, val (p+(0,a),t) = val (p,t)+(0,a)

theorem exists_flow {σ : ℂ → ℝ} (simple : SimpleMetric σ) : Nonempty (Flow σ) := by
  obtain ⟨τ,hτ,agree,⟨c,hc⟩,convex⟩ := exists_convex_extension simple
  have d : ContDiff ℝ ∞ (chartVector τ) :=
    contDiff_iff_contDiffAt.mpr fun p => ChartRegularity.chartVector_contDiffAt p hτ.contDiffAt
  obtain ⟨B,hB⟩ := bounds_of_constant_exterior hτ hc
  have lip : LipschitzWith B (chartVector τ) :=
    lipschitzWith_of_nnnorm_fderiv_le (d.differentiable (by simp)) (fun p => by exact_mod_cast (hB p).2)
  obtain ⟨Φ,hΦ,h0,D,group⟩ := GlobalGeodesicFlow.exists_flow d lip (fun p => (hB p).1)
  refine ⟨τ,hτ,agree,convex,Φ,hΦ,h0,D,group,?_⟩
  intro p a ha t
  have shift (y : State) : chartVector τ (y+(0,a)) = chartVector τ y := by
    simp [chartVector, Circle.exp_add, ha]
  have eq := ODE_solution_unique_of_mem_Ioo (v := fun _ => chartVector τ) (s := fun _ => univ)
    (a := -(|t|+1)) (b := |t|+1) (t₀ := 0) (fun _ _ => lip.lipschitzOnWith)
    (by constructor <;> linarith [abs_nonneg t])
    (fun s _ => ⟨D (p+(0,a)) s,trivial⟩) (g := fun s => Φ (p,s)+(0,a))
    (fun s _ => ⟨by simpa only [shift] using (D p s).add_const ((0,a) : State),trivial⟩) (by simp [h0])
  exact eq (x := t) (by constructor <;> linarith [le_abs_self t, neg_abs_le t])

namespace Flow

variable {σ : ℂ → ℝ} (F : Flow σ)

abbrev base (p : State) (t : ℝ) := (F.val (p,t)).1
abbrev angle (p : State) (t : ℝ) := (F.val (p,t)).2

theorem geo (p : State) (s : Set ℝ) : unitGeodesicOn F.factor (F.base p) (F.angle p) s := by
  intro t _
  exact ⟨((ContinuousLinearMap.fst ℝ ℂ ℝ).hasFDerivAt.comp_hasDerivAt t (F.ode p t)).hasDerivWithinAt,
    ((ContinuousLinearMap.snd ℝ ℂ ℝ).hasFDerivAt.comp_hasDerivAt t (F.ode p t)).hasDerivWithinAt⟩

theorem germ {z : ℂ} (hz : ‖z‖ ≤ 1) : F.factor =ᶠ[𝓝 z] σ := by
  obtain ⟨e,he,h⟩ := F.agrees
  have hsq : normSq z < 1+e := by rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg z]
  exact (Complex.continuous_normSq.continuousAt.eventually_lt_const hsq).mono fun y hy => h y hy

theorem curvature_germ {z : ℂ} (hz : ‖z‖ ≤ 1) : curvature F.factor z = curvature σ z := by
  have h := F.germ hz
  have g (u : ℂ) : (fun p => fderiv ℝ F.factor p u) =ᶠ[𝓝 z] fun p => fderiv ℝ σ p u :=
    h.fderiv.mono fun y hy => congrArg (fun l : ℂ →L[ℝ] ℝ => l u) hy
  simp [curvature,laplacian,h.eq_of_nhds,(g 1).fderiv_eq,(g I).fderiv_eq]

theorem stays {p : State} {t R : ℝ} (hR : 1 ≤ R) (h0 : ‖p.1‖ ≤ R) (he : ‖F.base p t‖ ≤ R) :
    ∀ s ∈ Icc 0 t, ‖F.base p s‖ ≤ R :=
  stays_in_disk (F.geo p _) (by simpa [base,F.initial] using h0) he
    (fun z hz => F.convex z (hR.trans hz.le))

private def cylinder (R : ℝ) : Set State := closedBall (0:ℂ) R ×ˢ Icc (-Real.pi) Real.pi

private theorem compact_cylinder (R : ℝ) : IsCompact (cylinder R) :=
  (isCompact_closedBall _ _).prod isCompact_Icc

/-- One elapsed time works for all rays launched anywhere in a slightly
larger closed disk, in every direction on the lifted angular cover. -/
theorem uniform_escape (simple : SimpleMetric σ) :
    ∃ T > 0, ∃ R > 1, R ≤ 2 ∧ ∀ p : State, ‖p.1‖ ≤ R → R < ‖F.base p T‖ := by
  classical
  have escape (p : State) (hp : ‖p.1‖ ≤ 1) : ∃ t > 0, 1 < ‖F.base p t‖ := by
    apply ScalarGeneralUnrestricted.forward_escape simple (fun s => F.val (p,s))
      (by simpa [F.initial] using hp)
    intro s hs
    have h := F.germ (mem_closedBall_zero_iff.mp hs)
    simpa only [chartVector, Isothermal.angularDrift, h.fderiv_eq,h.eq_of_nhds] using F.ode p s
  let K := cylinder 1
  choose t ht he using fun y : K => escape y (by simpa using y.property.1)
  let U := fun y : K => {p : State | 1 < ‖F.base p (t y)‖}
  have hu (y : K) : IsOpen (U y) := isOpen_lt continuous_const <|
    (continuous_fst.comp (F.smooth.continuous.comp (continuous_id.prodMk continuous_const))).norm
  obtain ⟨A,covers⟩ := (compact_cylinder 1).elim_finite_subcover U hu
    (fun p hp => mem_iUnion.mpr ⟨⟨p,hp⟩,he ⟨p,hp⟩⟩)
  let T := 1 + ∑ y ∈ A, t y
  have hT : 0 < T := add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg (fun i _ => (ht i).le))
  have outs (p : State) (hp : p ∈ K) : 1 < ‖F.base p T‖ := by
    obtain ⟨y,hy,h⟩ := mem_iUnion₂.mp (covers hp)
    have le : t y ≤ T := by
      have sum := Finset.single_le_sum (f := t) (fun i _ => (ht i).le) hy
      dsimp [T]; linarith
    by_contra! lock
    exact (not_lt_of_ge (F.stays le_rfl (by simpa using hp.1) lock _ ⟨(ht y).le,le⟩)) h
  let M := fun p : State => max ‖p.1‖ ‖F.base p T‖
  have hm : Continuous M := continuous_fst.norm.max
    ((continuous_fst.comp (F.smooth.continuous.comp (continuous_id.prodMk continuous_const))).norm)
  obtain ⟨m,mm,hmin⟩ := (compact_cylinder 2).exists_isMinOn
    (show (cylinder 2).Nonempty from ⟨(0,0),by simp [cylinder,Real.pi_pos.le]⟩) hm.continuousOn
  have hM : 1 < M m := by
    by_cases h : ‖m.1‖ ≤ 1
    · exact (outs m ⟨by simpa using h,mm.2⟩).trans_le (le_max_right ..)
    · exact (lt_of_not_ge h).trans_le (le_max_left ..)
  let R := min ((1+M m)/2) 2
  have hR : 1 < R := lt_min (by linarith) (by norm_num)
  have hRM : R < M m := (min_le_left ..).trans_lt (by linarith)
  refine ⟨T,hT,R,hR,min_le_right ..,?_⟩
  intro p hp
  let a := (Circle.exp p.2 : ℂ).arg - p.2
  have a1 : Circle.exp a = 1 := by
    have e : Circle.exp (Circle.exp p.2 : ℂ).arg = Circle.exp p.2 := Circle.exp_arg _
    simp only [a,sub_eq_add_neg,Circle.exp_add,Circle.exp_neg,e,mul_inv_cancel]
  let q := p+(0,a)
  have qθ : q.2 = (Circle.exp p.2 : ℂ).arg := by simp [q,a]
  have hq : q ∈ cylinder 2 := ⟨by simpa [q] using hp.trans (min_le_right ..),qθ ▸
    ⟨(Complex.neg_pi_lt_arg _).le,Complex.arg_le_pi _⟩⟩
  have e : F.base q T = F.base p T := by simpa [base,q] using congrArg Prod.fst (F.periodic p a a1 T)
  have h := hRM.trans_le (isMinOn_iff.mp hmin q hq)
  change R < max ‖p.1 + 0‖ ‖F.base q T‖ at h
  simp [e,not_lt_of_ge hp] at h
  exact h

def curvaturePath (T : ℝ) (p : State) : C(Icc 0 T,ℝ) :=
  ⟨fun t => curvature F.factor (F.base p t), (curvature_contDiff F.smoothFactor).continuous.comp
    (continuous_fst.comp (F.smooth.continuous.comp (continuous_const.prodMk continuous_subtype_val)))⟩

theorem curvaturePath_continuous (T : ℝ) : Continuous (F.curvaturePath T) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact (curvature_contDiff F.smoothFactor).continuous.comp (continuous_fst.comp
    (F.smooth.continuous.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))))

attribute [local irreducible] field speed

def quotient {T : ℝ} (hT : 0 ≤ T) (u : State × ℝ) :=
  ∫ s : ℝ in (0:ℝ)..1, speed hT (F.curvaturePath T u.1) (s*u.2)

theorem quotient_continuous {T : ℝ} (hT : 0 ≤ T) : Continuous (F.quotient hT) := by
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun (u : State × ℝ) (s : ℝ) => speed hT (F.curvaturePath T u.1) (s*u.2))
  change Continuous (fun x : (State × ℝ) × ℝ => speed hT (F.curvaturePath T x.1.1) (x.2*x.1.2))
  exact (speed_continuous hT).comp (((F.curvaturePath_continuous T).comp (continuous_fst.comp continuous_fst)).prodMk
    (continuous_snd.mul (continuous_snd.comp continuous_fst)))

theorem quotient_zero {T : ℝ} (hT : 0 ≤ T) (p : State) : F.quotient hT (p,0) = 1 := by
  simp [quotient,(initial_values hT _).2]

theorem field_eq_mul_quotient {T t : ℝ} (hT : 0 ≤ T) (p : State) (ht : t ∈ Icc 0 T) :
    field hT (F.curvaturePath T p) t = t * F.quotient hT (p,t) := by
  let k := F.curvaturePath T p
  have hzero := (initial_values hT k).1
  rcases eq_or_lt_of_le ht.1 with rfl | h
  · simpa [k] using hzero
  have c : Continuous (fun s : ℝ => field hT k (s*t)) := (field_continuous hT).comp (continuous_const.prodMk (continuous_id.mul continuous_const))
  have v : Continuous (fun s : ℝ => speed hT k (s*t)) := (speed_continuous hT).comp (continuous_const.prodMk (continuous_id.mul continuous_const))
  have hd (s : ℝ) (hs : s ∈ Ioo (0:ℝ) 1) :
      HasDerivAt (fun s => field hT k (s*t)) (t * speed hT k (s*t)) s := by
    have hi : s*t ∈ Ioo 0 T := ⟨mul_pos hs.1 h, (mul_lt_of_lt_one_left h hs.2).trans_le ht.2⟩
    have dc := ((solves hT k _ (Ioo_subset_Icc_self hi)).1).hasDerivAt (Icc_mem_nhds hi.1 hi.2)
    simpa [mul_comm] using dc.comp s ((hasDerivAt_id s).mul_const t)
  have eq := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one
    (f := fun s => field hT k (s*t)) c.continuousOn hd ((continuous_const.mul v).intervalIntegrable _ _)
  rw [intervalIntegral.integral_const_mul] at eq
  simp only [one_mul,zero_mul,hzero,sub_zero] at eq
  exact eq.symm

private theorem compact_margin {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {r f : X → ℝ} (cr : Continuous r) (cf : Continuous f)
    (pos : ∀ x ∈ K, r x ≤ 1 → 0 < f x) :
    ∃ R > 1, ∃ c > 0, ∀ x ∈ K, r x ≤ R → c ≤ f x := by
  let B := K ∩ {x | f x ≤ 0}
  have cb : IsCompact B := hK.inter_right (isClosed_le cf continuous_const)
  have grow : ∃ R > 1, ∀ x ∈ K, r x ≤ R → 0 < f x := by
    by_cases he : B.Nonempty
    · obtain ⟨y,hy,hmin⟩ := cb.exists_isMinOn he cr.continuousOn
      have h := lt_of_not_ge (fun e => (not_lt_of_ge hy.2) (pos y hy.1 e))
      refine ⟨(1+r y)/2,by linarith,?_⟩
      intro x hx hr
      by_contra! hn
      linarith [isMinOn_iff.mp hmin x ⟨hx,hn⟩]
    · exact ⟨2,by norm_num,fun x hx _ => lt_of_not_ge (fun e => he ⟨x,hx,e⟩)⟩
  obtain ⟨R,hR,g⟩ := grow
  by_cases h : (K ∩ {x | r x ≤ R}).Nonempty
  · obtain ⟨x,hx,hmin⟩ := (hK.inter_right (isClosed_le cr continuous_const)).exists_isMinOn h cf.continuousOn
    exact ⟨R,hR,f x,g x hx.1 hx.2, fun y hy hr => isMinOn_iff.mp hmin y ⟨hy,hr⟩⟩
  · exact ⟨R,hR,1,zero_lt_one,fun y hy hr => (h ⟨y,hy,hr⟩).elim⟩

theorem normalized_positive {T t : ℝ} (hT : 0 ≤ T) (simple : SimpleMetric σ)
    {p : State} (hp : ‖p.1‖ ≤ 1) (ht : t ∈ Icc 0 T) (hend : ‖F.base p t‖ ≤ 1) :
    0 < F.quotient hT (p,t) := by
  rcases eq_or_lt_of_le ht.1 with rfl | h
  · rw [F.quotient_zero]; exact zero_lt_one
  have inside := F.stays le_rfl hp hend
  let k := F.curvaturePath T p
  have ray : unitGeodesicOn σ (F.base p) (F.angle p) (Icc 0 t) := by
    intro s hs
    have eq := F.germ (inside s hs)
    simpa only [Isothermal.angularDrift,eq.eq_of_nhds,eq.fderiv_eq] using F.geo p (Icc 0 t) s hs
  have jc : jacobiOn σ (F.base p) (field hT k) (speed hT k) (Icc 0 t) := by
    intro s hs
    have sub : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc_right ht.2
    obtain ⟨j,dj⟩ := solves hT k s (sub hs)
    exact ⟨j.mono sub,by simpa only [k,curvaturePath,ContinuousMap.coe_mk,F.curvature_germ (inside s hs)] using dj.mono sub⟩
  have j := normalized_jacobi_positive simple h ray (fun s hs => mem_closedBall_zero_iff.mpr (inside s hs))
    jc (initial_values hT k).1 (initial_values hT k).2
  rw [F.field_eq_mul_quotient hT p ht] at j
  exact (mul_pos_iff_of_pos_left h).mp j

/-- A uniform positive margin for the normalized Jacobi determinant on every
segment in a slightly enlarged disk, including arbitrarily short segments. -/
theorem jacobi_margin {T : ℝ} (hT : 0 ≤ T) (simple : SimpleMetric σ) :
    ∃ R > 1, R ≤ 2 ∧ ∃ c > 0, ∀ p : State, ‖p.1‖ ≤ R → ∀ t ∈ Icc 0 T, ‖F.base p t‖ ≤ R →
      c ≤ F.quotient hT (p,t) := by
  let K := cylinder 2 ×ˢ Icc 0 T
  let rad := fun u : State × ℝ => max ‖u.1.1‖ ‖F.base u.1 u.2‖
  have cr : Continuous rad := (continuous_fst.comp continuous_fst).norm.max
    (continuous_fst.comp F.smooth.continuous).norm
  obtain ⟨R,hr,c,hc,g⟩ := compact_margin ((compact_cylinder 2).prod isCompact_Icc) cr
    (F.quotient_continuous hT) (fun u hu h => F.normalized_positive hT simple
      (max_le_iff.mp h).1 hu.2 (max_le_iff.mp h).2)
  refine ⟨min R 2,lt_min hr (by norm_num),min_le_right ..,c,hc,?_⟩
  intro p hp t ht he
  let a := (Circle.exp p.2 : ℂ).arg - p.2
  have ea : Circle.exp a = 1 := by
    have e : Circle.exp (Circle.exp p.2 : ℂ).arg = Circle.exp p.2 := Circle.exp_arg _
    simp only [a,sub_eq_add_neg,Circle.exp_add,Circle.exp_neg,e,mul_inv_cancel]
  let q := p+(0,a)
  have angleQ : q.2 = (Circle.exp p.2 : ℂ).arg := by simp [q,a]
  have qK : (q,t) ∈ K := ⟨⟨by simpa [q] using hp.trans (min_le_right ..),angleQ ▸
    ⟨(Complex.neg_pi_lt_arg _).le, Complex.arg_le_pi _⟩⟩,ht⟩
  have beq (s : ℝ) : F.base q s = F.base p s := by
    simpa [base,q] using congrArg Prod.fst (F.periodic p a ea s)
  have keq : F.curvaturePath T q = F.curvaturePath T p := by ext s; simp [curvaturePath,beq]
  have good := g (q,t) qK (max_le (by simpa [q] using hp.trans (min_le_left ..))
    ((beq t).symm ▸ he.trans (min_le_left ..)))
  simpa only [quotient,keq] using good

end Flow
end TransportOkaGrauert.JacobiEnlargement
