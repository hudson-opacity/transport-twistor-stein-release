import TransportOkaGrauert.FourierDecay
import TransportOkaGrauert.ScalarGeneralCauchy
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-! # Uniform rapid decay for parametrized angular coefficients
The estimates hold on each compact set of parameters and remain available
after differentiation with respect to arbitrary base variables. -/

namespace TransportOkaGrauert.SmoothFourierFamily
noncomputable section
open Complex Metric Set MeasureTheory AddCircle Filter
open scoped ContDiff Topology
variable {B : Type} [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]
abbrev period := 2 * Real.pi
local instance : Fact (0 < period) := ⟨Real.two_pi_pos⟩

def PeriodicFamily (g : B × ℝ → ℂ) := ∀ p t, g (p,t+period) = g (p,t)
def coeff (g : B × ℝ → ℂ) (n : ℤ) (p : B) := fourierCoeffOn Real.two_pi_pos (fun t => g (p,t)) n
def direction (g : B × ℝ → ℂ) (v : B × ℝ) (x : B × ℝ) := fderiv ℝ g x v

omit [FiniteDimensional ℝ B] in
theorem partial_smooth {g : B × ℝ → ℂ} (h : ContDiff ℝ ∞ g) (v : B × ℝ) :
    ContDiff ℝ ∞ (direction g v) := (h.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

omit [FiniteDimensional ℝ B] in
theorem partial_periodic {g : B × ℝ → ℂ} (h : PeriodicFamily g) (v : B × ℝ) :
    PeriodicFamily (direction g v) := by
  intro p t
  let a : B × ℝ := (0,period)
  have he : (fun x : B × ℝ => g (x+a)) = g := funext fun x => by rcases x with ⟨p,t⟩; change g (p+0,t+period) = _; simpa using h p t
  have H := congrArg (fun f : B × ℝ → ℂ => fderiv ℝ f (p,t) v) he
  simpa [direction,fderiv_comp_add_right,a] using H

private def weight (n : ℤ) (t : ℝ) := fourier (-n) (t : AddCircle period)
private theorem weight_smooth (n : ℤ) : ContDiff ℝ ∞ (weight n) := by
  unfold weight
  simp only [fourier_coe_apply]
  have hc : ContDiff ℝ ∞ (fun t : ℝ => (t:ℂ)) := Complex.ofRealCLM.contDiff
  fun_prop

omit [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B] in
private theorem coeff_eq (g : B × ℝ → ℂ) (n : ℤ) :
    coeff g n = fun p => (1/period : ℝ) • ∫ t in (0:ℝ)..period, weight n t * g (p,t) := by
  funext p
  rw [coeff,fourierCoeffOn_eq_integral]
  simp [weight]

theorem coeff_smooth {g : B × ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (n : ℤ) :
    ContDiff ℝ ∞ (coeff g n) := by
  rw [coeff_eq]
  exact (ScalarGeneralCauchy.integral_smooth (((weight_smooth n).comp contDiff_snd).mul hg) Real.two_pi_pos).const_smul _

theorem coeff_direction {g : B × ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (n : ℤ) (p v : B) :
    fderiv ℝ (coeff g n) p v = coeff (direction g (v,0)) n p := by
  rw [coeff_eq,coeff_eq]
  let h (a : B × ℝ) := weight n a.2 * g a
  have hh : ContDiff ℝ ∞ h := ((weight_smooth n).comp contDiff_snd).mul hg
  have H := (ScalarGeneralCauchy.integral_smooth hh Real.two_pi_pos).differentiable (by simp) p
  change fderiv ℝ ((1/period : ℝ) • (fun y => ∫ t in (0:ℝ)..period, h (y,t))) p v = _
  rw [(H.hasFDerivAt.const_smul (1/period:ℝ)).fderiv,ContinuousLinearMap.smul_apply,
    ScalarGeneralCauchy.integral_direction hh p v Real.two_pi_pos]
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  have dg := (hg.differentiable (by simp) (p,t)).hasFDerivAt.comp p
    ((hasFDerivAt_id (𝕜 := ℝ) p).prodMk (hasFDerivAt_const t p))
  exact DFunLike.congr_fun (dg.const_mul (weight n t)).fderiv v

omit [FiniteDimensional ℝ B] in
theorem angular_coeff {g : B × ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (hp : PeriodicFamily g)
    {n : ℤ} (hn : n ≠ 0) (p : B) :
    coeff (direction g (0,1)) n p = (I*n) * coeff g n p := by
  let f (s : ℝ) := g (p,s)
  have fs : ContDiff ℝ ∞ f := hg.comp (contDiff_const.prodMk contDiff_id)
  have der (t : ℝ) : deriv f t = direction g (0,1) (p,t) := by
    have line : HasDerivAt (fun s : ℝ => (p,s)) (0,1) t := (hasDerivAt_const t p).prodMk (hasDerivAt_id t)
    have h := (hg.differentiable (by simp) (p,t)).hasFDerivAt.comp_hasDerivAt t line
    exact h.deriv
  rw [coeff,← funext der]
  exact FourierDecay.derivative_coefficient f (hp p) (fs.differentiable (by simp))
    (fs.continuous_deriv (by simp)) n hn

omit [FiniteDimensional ℝ B] in
private theorem uniform_bound {g : B × ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (K : Set B) (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ K, ∀ n, ‖coeff g n p‖ ≤ C := by
  obtain ⟨M,hM⟩ := (hK.prod (isCompact_Icc (a := (0:ℝ)) (b := period))).bddAbove_image hg.continuous.norm.continuousOn
  let C := max M 0
  refine ⟨C,le_max_right ..,fun p hp n => ?_⟩
  rw [coeff_eq, norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ 1/period)]
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := period) (C := C)
    (f := fun t => weight n t * g (p,t)) (fun t ht => by
      rw [uIoc_of_le Real.two_pi_pos.le] at ht
      rw [norm_mul,show ‖weight n t‖ = 1 from Circle.norm_coe _,one_mul]
      exact (hM ⟨(p,t),⟨hp,Ioc_subset_Icc_self ht⟩,rfl⟩).trans (le_max_left ..))
  rw [sub_zero,abs_of_nonneg Real.two_pi_pos.le] at hi
  calc
    _ ≤ (1/period) * (C*period) := mul_le_mul_of_nonneg_left hi (by positivity)
    _ = C := by field_simp [Real.two_pi_pos.ne']

omit [FiniteDimensional ℝ B] in
/-- Every power of the frequency is controlled uniformly on compact parameter sets. -/
theorem rapid {g : B × ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (hp : PeriodicFamily g)
    (K : Set B) (hK : IsCompact K) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ K, ∀ n : ℕ, 0 < n → (n:ℝ)^k * ‖coeff g n p‖ ≤ C := by
  induction k generalizing g with
  | zero =>
    obtain ⟨C,hc,h⟩ := uniform_bound hg K hK
    exact ⟨C,hc,fun p hP n _ => by simpa using h p hP n⟩
  | succ k ih =>
    obtain ⟨C,hC,h⟩ := ih (partial_smooth hg (0,1)) (partial_periodic hp (0,1))
    refine ⟨C,hC,fun p hP n hn => ?_⟩
    have eq := h p hP n hn
    rw [angular_coeff hg hp (by exact_mod_cast hn.ne') p,norm_mul,norm_mul,norm_I,one_mul,
      norm_intCast,Int.cast_natCast,abs_of_nonneg (Nat.cast_nonneg n)] at eq
    simpa only [pow_succ,mul_assoc] using eq
/-- A uniform bound for all unit parameter directions gives rapid decay in
operator norm for the derivative of each Fourier coefficient. -/
theorem rapid_derivative {g : B × ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (hp : PeriodicFamily g)
    (K : Set B) (hK : IsCompact K) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ K, ∀ n : ℕ, 0 < n →
      (n:ℝ)^k * ‖fderiv ℝ (coeff g n) p‖ ≤ C := by
  let G (x : (B × B) × ℝ) := direction g (x.1.2,0) (x.1.1,x.2)
  have hG : ContDiff ℝ ∞ G :=
    ((hg.fderiv_right (m := ∞) (by simp)).comp ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd)).clm_apply
      ((contDiff_snd.comp contDiff_fst).prodMk contDiff_const)
  have pG : PeriodicFamily G := fun p t => partial_periodic hp (p.2,0) p.1 t
  obtain ⟨C,hC,h⟩ := rapid hG pG (K ×ˢ closedBall (0:B) 1) (hK.prod (isCompact_closedBall _ _)) k
  refine ⟨C,hC,fun p hp' n hn => ?_⟩
  have hpos : 0 < (n:ℝ)^k := by positivity
  rw [mul_comm, ← le_div_iff₀ hpos]
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (div_nonneg hC hpos.le)
  intro v hv
  rw [coeff_direction hg,le_div_iff₀ hpos,mul_comm]
  exact h (p,v) ⟨hp',by simpa using hv.le⟩ n hn

end
end TransportOkaGrauert.SmoothFourierFamily
