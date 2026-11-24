import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! # A reference operator of order minus one in conformal coordinates
The exponentially damped Euclidean ray average acts diagonally on ordinary
plane waves. Its multiplier is exactly the inverse square root of 1+|ξ|².
The damping keeps the zero frequency finite while preserving the principal
singularity of the scalar geodesic normal operator. -/
namespace TransportOkaGrauert.FlatNormalSymbol
noncomputable section
open Complex MeasureTheory Set Metric AddCircle
open scoped ComplexConjugate ContDiff Topology
private abbrev Angle := AddCircle (2*Real.pi)
local instance : Fact (0 < 2*Real.pi) := ⟨Real.two_pi_pos⟩

def directionPair (ξ w : ℂ) : ℝ := (conj ξ*w).re
def wave (ξ z : ℂ) := Complex.exp (I*(directionPair ξ z : ℂ))

def rayAverage (f : ℂ → ℂ) (z : ℂ) :=
  ∫ θ : Angle, (∫ t : ℝ in Ioi 0, (Real.exp (-t):ℂ)*f (z + t • (θ.toCircle : ℂ))) ∂haarAddCircle

private theorem damped (ξ z w : ℂ) :
    (∫ t : ℝ in Ioi 0, (Real.exp (-t):ℂ)*wave ξ (z+t • w)) =
      wave ξ z * (1-I*(directionPair ξ w:ℂ))⁻¹ := by
  let c := -1+I*(directionPair ξ w:ℂ)
  have hc : c.re < 0 := by simp [c]
  have eval (t : ℝ) : (Real.exp (-t):ℂ)*wave ξ (z+t • w) = wave ξ z * Complex.exp (c*t) := by
    have E : directionPair ξ (z+t • w) = directionPair ξ z + t*directionPair ξ w := by
      simp [directionPair,mul_add,real_smul]
      ring
    simp only [wave,E,ofReal_exp,← Complex.exp_add,c,ofReal_add,ofReal_mul,ofReal_neg]
    congr 1
    ring
  simp_rw [eval]
  rw [integral_const_mul,integral_exp_mul_complex_Ioi hc]
  simp only [ofReal_zero,mul_zero,Complex.exp_zero]
  congr 1
  dsimp [c]
  rw [show -1+I*(directionPair ξ w:ℂ) = -(1-I*(directionPair ξ w:ℂ)) by ring]
  rw [div_eq_mul_inv,inv_neg,neg_one_mul,neg_neg]

private abbrev Alg := C(Angle,ℂ)
private def meanL : Alg →L[ℂ] ℂ := (L1.integralCLM' ℂ).comp (ContinuousMap.toLp 1 haarAddCircle ℂ)
private theorem meanL_apply (f : Alg) : meanL f = ∫ θ, f θ ∂haarAddCircle := by
  unfold meanL
  rw [ContinuousLinearMap.comp_apply,← L1.integral_eq',L1.integral_eq_integral]
  exact integral_congr_ae (ContinuousMap.coeFn_toLp haarAddCircle f)

private theorem mean_resolvent {c : ℂ} (hc : ‖c‖ < 1) (k : ℤ) (hk : k ≠ 0) :
    (∫ θ : Angle, (1-c*fourier k θ)⁻¹ ∂haarAddCircle) = 1 := by
  let Q : Alg := c • fourier k
  have sm := summable_geometric_of_norm_lt_one (show ‖Q‖ < 1 by simpa [Q,norm_smul,fourier_norm] using hc)
  have eval (θ : Angle) : (∑' n : ℕ, Q^n) θ = (1-c*fourier k θ)⁻¹ := by
    let ev : Alg →L[ℂ] ℂ := ContinuousMap.evalCLM ℂ θ
    change ev (∑' n : ℕ, Q^n) = _
    rw [ev.map_tsum sm]
    change (∑' n : ℕ, (c*fourier k θ)^n) = _
    apply tsum_geometric_of_norm_lt_one
    simpa only [norm_mul,show ‖fourier k θ‖ = 1 from Circle.norm_coe _,mul_one] using hc
  have powers (n : ℕ) : Q^n = c^n • fourier ((n:ℤ)*k) := by
    induction n with
    | zero => ext θ; simp
    | succ n ih =>
      ext θ
      simp only [pow_succ,ih,ContinuousMap.mul_apply,ContinuousMap.smul_apply,smul_eq_mul,Nat.cast_succ,
        add_mul,one_mul,fourier_add,Q]
      ring
  have scalar (j : ℤ) : meanL (fourier j) = if j = 0 then 1 else 0 := by
    have H := congrFun (fourierCoeff_fourier (T := (2*Real.pi)) j) 0
    rw [meanL_apply]
    simpa [fourierCoeff,Pi.single_apply,eq_comm] using H
  rw [← funext eval,←meanL_apply,meanL.map_tsum sm,tsum_eq_single 0]
  · rw [pow_zero,meanL_apply]; simp
  · intro n hn
    rw [powers,map_smul,scalar,if_neg (mul_ne_zero (by exact_mod_cast hn) hk),smul_zero]

private theorem mean_inverse (ξ : ℂ) :
    (∫ θ : Angle, (1-I*(directionPair ξ θ.toCircle:ℂ))⁻¹ ∂haarAddCircle) =
      ((Real.sqrt (1+‖ξ‖^2) : ℝ):ℂ)⁻¹ := by
  let d := Real.sqrt (1+‖ξ‖^2)
  have dpos : 0 < d := Real.sqrt_pos.mpr (by positivity)
  have dsq : d^2 = 1+‖ξ‖^2 := Real.sq_sqrt (by positivity)
  have bigger : ‖ξ‖ < 1+d := by nlinarith [norm_nonneg ξ]
  let b := I*conj ξ/(1+(d:ℂ))
  let c := I*ξ/(1+(d:ℂ))
  have nd : ‖(1:ℂ)+(d:ℂ)‖ = 1+d := by
    rw [← ofReal_one,← ofReal_add,norm_real,Real.norm_of_nonneg (by positivity)]
  have hb : ‖b‖ < 1 := by simpa [b,norm_div,norm_mul,nd,div_lt_one (by positivity : 0 < 1+d)] using bigger
  have hc : ‖c‖ < 1 := by simpa [c,norm_div,norm_mul,nd,div_lt_one (by positivity : 0 < 1+d)] using bigger
  have exact (w : Circle) : (1-I*(directionPair ξ w:ℂ))⁻¹ =
      (d:ℂ)⁻¹ * ((1-b*(w:ℂ))⁻¹ + (1-c*conj (w:ℂ))⁻¹ - 1) := by
    have nonzero {v : ℂ} (h : ‖v‖ < 1) : 1-v ≠ 0 :=
      sub_ne_zero.mpr (fun eq => by rw [← eq,norm_one] at h; exact lt_irrefl _ h)
    have h₁ : (1:ℂ)-b*(w:ℂ) ≠ 0 := nonzero (by simpa [norm_mul] using hb)
    have h₂ : (1:ℂ)-c*conj (w:ℂ) ≠ 0 := nonzero (by simpa [norm_mul] using hc)
    have h₃ : (1:ℂ)-I*(directionPair ξ w:ℂ) ≠ 0 := by intro e; simpa using congrArg Complex.re e
    have hd : (d:ℂ) ≠ 0 := ofReal_ne_zero.mpr dpos.ne'
    have hden : (1:ℂ)+(d:ℂ) ≠ 0 := norm_ne_zero_iff.mp (nd.trans_ne (by positivity))
    have hunit : (w:ℂ)*conj (w:ℂ) = 1 := by rw [Complex.mul_conj,Complex.normSq_eq_norm_sq]; simp
    have hh : (d:ℂ)^2 = 1+ξ*conj ξ := by rw [Complex.mul_conj,Complex.normSq_eq_norm_sq]; exact_mod_cast dsq
    have pair : (directionPair ξ w:ℂ) = (conj ξ*(w:ℂ)+ξ*conj (w:ℂ))/2 := by
      unfold directionPair
      rw [Complex.re_eq_add_conj,map_mul,starRingEnd_self_apply]
    let A := b*(w:ℂ)
    let B := c*conj (w:ℂ)
    have prod : A*B = (1-(d:ℂ))/(1+(d:ℂ)) := calc
      _ = I^2*(ξ*conj ξ)*((w:ℂ)*conj (w:ℂ))/(1+(d:ℂ))^2 := by dsimp only [A,B,b,c]; field_simp [hden]
      _ = _ := by
        rw [Complex.I_sq,hunit,show ξ*conj ξ = (d:ℂ)^2-1 by linear_combination -hh]
        field_simp [hden]
        ring
    have sum : A+B = 2*I*(directionPair ξ w:ℂ)/(1+(d:ℂ)) := by dsimp only [A,B,b,c]; rw [pair]; ring
    have denom : (1-A)*(1-B) = 2*(1-I*(directionPair ξ w:ℂ))/(1+(d:ℂ)) := by
      rw [show (1-A)*(1-B) = 1-(A+B)+A*B by ring,sum,prod]
      field_simp [hden]; ring
    have frac : (1-A)⁻¹ + (1-B)⁻¹ - 1 = (1-A*B)/((1-A)*(1-B)) := by
      field_simp [show 1-A ≠ 0 from h₁,show 1-B ≠ 0 from h₂]
      ring
    change _ = (d:ℂ)⁻¹ * ((1-A)⁻¹+(1-B)⁻¹-1)
    rw [frac,denom,prod]
    field_simp [hd,hden,h₃]
    ring
  have h₁ : Integrable (fun θ : Angle => (1-b*fourier 1 θ)⁻¹) haarAddCircle := by
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    exact (continuous_const.sub (continuous_const.mul (fourier 1).continuous)).inv₀
      (fun θ h => by
        change 1-b*fourier 1 θ = 0 at h
        have H := congrArg norm (sub_eq_zero.mp h)
        rw [norm_one,norm_mul,show ‖fourier _ θ‖ = 1 from Circle.norm_coe _,mul_one] at H
        linarith)
  have h₂ : Integrable (fun θ : Angle => (1-c*fourier (-1) θ)⁻¹) haarAddCircle := by
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    exact (continuous_const.sub (continuous_const.mul (fourier (-1)).continuous)).inv₀
      (fun θ h => by
        change 1-c*fourier (-1) θ = 0 at h
        have H := congrArg norm (sub_eq_zero.mp h)
        rw [norm_one,norm_mul,show ‖fourier _ θ‖ = 1 from Circle.norm_coe _,mul_one] at H
        linarith)
  have form (θ : Angle) : (1-I*(directionPair ξ θ.toCircle:ℂ))⁻¹ = (d:ℂ)⁻¹ * ((1-b*fourier 1 θ)⁻¹ + (1-c*fourier (-1) θ)⁻¹ - 1) := by
    rw [fourier_neg (n := (1:ℤ)),fourier_one]; exact exact θ.toCircle
  simp_rw [form]
  have plus : Integrable (fun θ : Angle => (1-b*fourier 1 θ)⁻¹ + (1-c*fourier (-1) θ)⁻¹) haarAddCircle := h₁.add h₂
  rw [integral_const_mul,integral_sub plus (integrable_const (1:ℂ)),integral_add h₁ h₂,
    mean_resolvent hb 1 (by norm_num),mean_resolvent hc (-1) (by norm_num)]
  simp [d]

/-- Exact positive Fourier multiplier of the damped Euclidean ray average
on every plane wave, including frequency zero. -/
theorem plane_wave (ξ z : ℂ) :
    rayAverage (wave ξ) z = wave ξ z * ((Real.sqrt (1+‖ξ‖^2):ℝ):ℂ)⁻¹ := by
  unfold rayAverage
  simp_rw [damped]
  rw [integral_const_mul, mean_inverse]

private theorem norm_wave (ξ z : ℂ) : ‖wave ξ z‖ = 1 := by simp [wave,Complex.norm_exp]

/-- For an absolutely convergent superposition of plane waves the actual ray
integrals may be taken term by term. -/
theorem series_action {ι : Type} [Countable ι] (a : ι → ℂ) (ξ : ι → ℂ)
    (ha : Summable fun i => ‖a i‖) (z : ℂ) :
    rayAverage (fun x => ∑' i, a i * wave (ξ i) x) z =
      ∑' i, a i * wave (ξ i) z * ((Real.sqrt (1+‖ξ i‖^2):ℝ):ℂ)⁻¹ := by
  let oneRay (i : ι) (w : Circle) (t : ℝ) := (Real.exp (-t):ℂ)*(a i*wave (ξ i) (z+t • (w:ℂ)))
  let H (i : ι) (θ : Angle) := a i * wave (ξ i) z * (1-I*(directionPair (ξ i) θ.toCircle:ℂ))⁻¹
  have bound (i : ι) (w : Circle) (t : ℝ) : ‖oneRay i w t‖ = Real.exp (-t)*‖a i‖ := by
    simp only [oneRay,norm_mul,norm_wave,mul_one,Complex.norm_real,Real.norm_of_nonneg (Real.exp_pos _).le]
  have integ (i : ι) (w : Circle) : IntegrableOn (oneRay i w) (Ioi 0) := by
    apply ((integrableOn_exp_neg_Ioi 0).mul_const ‖a i‖).mono'
    · have c : Continuous (oneRay i w) := by unfold oneRay wave directionPair; fun_prop
      exact c.aestronglyMeasurable
    · exact .of_forall fun t => (bound i w t).le
  have sumInt (w : Circle) : Summable fun i => ∫ t : ℝ in Ioi 0, ‖oneRay i w t‖ := by
    simpa only [bound,integral_mul_const,integral_exp_neg_Ioi_zero,one_mul] using ha
  have inner (i : ι) (w : Circle) : (∫ t : ℝ in Ioi 0, oneRay i w t) =
      a i*wave (ξ i) z * (1-I*(directionPair (ξ i) w:ℂ))⁻¹ := by
    simp only [oneRay,mul_left_comm (↑(Real.exp _):ℂ) (a i),integral_const_mul,damped,mul_assoc]
  have value (θ : Angle) : (∫ t : ℝ in Ioi 0, (Real.exp (-t):ℂ)*(∑' i, a i*wave (ξ i) (z+t • (θ.toCircle:ℂ)))) =
      ∑' i, H i θ := by
    simp_rw [← tsum_mul_left]
    rw [← integral_tsum_of_summable_integral_norm (fun i => integ i θ.toCircle) (sumInt θ.toCircle)]
    exact tsum_congr fun i => inner i θ.toCircle
  have hH (i : ι) : Continuous (H i) := by
    have hn (x : ℝ) : 1-I*(x:ℂ) ≠ 0 := by intro eq; simpa using congrArg Complex.re eq
    unfold H directionPair
    apply continuous_const.mul
    exact (continuous_const.sub (continuous_const.mul (Complex.continuous_ofReal.comp
      (Complex.continuous_re.comp (continuous_const.mul (continuous_subtype_val.comp AddCircle.continuous_toCircle)))))).inv₀ fun _ => hn _
  have bH (i : ι) (θ : Angle) : ‖H i θ‖ ≤ ‖a i‖ := by
    rw [show H i θ = ∫ t : ℝ in Ioi 0, oneRay i θ.toCircle t from (inner i θ.toCircle).symm]
    apply (norm_integral_le_integral_norm _).trans
    simp only [bound,integral_mul_const,integral_exp_neg_Ioi_zero,one_mul,le_rfl]
  unfold rayAverage
  simp_rw [value]
  rw [← integral_tsum_of_summable_integral_norm (fun i => (hH i).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (ha.of_nonneg_of_le (fun i => integral_nonneg fun _ => norm_nonneg _) (fun i => by
      simpa using integral_mono_of_nonneg (μ := haarAddCircle) (.of_forall fun _ => norm_nonneg _) (integrable_const _) (.of_forall (bH i))))]
  apply tsum_congr
  intro i
  simp only [H,integral_const_mul,mean_inverse]

/-- Exact inverse for smooth periodic Fourier data. It suffices to assume the
single weighted summability bound used by the inverse. -/
theorem inverse_series {ι : Type} [Countable ι] (a : ι → ℂ) (ξ : ι → ℂ)
    (h : Summable fun i => Real.sqrt (1+‖ξ i‖^2)*‖a i‖) :
    ∃ g : ℂ → ℂ, ∀ z, rayAverage g z = ∑' i, a i * wave (ξ i) z := by
  let b (i : ι) := (Real.sqrt (1+‖ξ i‖^2):ℂ)*a i
  have hb : Summable fun i => ‖b i‖ := by simpa [b,norm_mul,Real.norm_of_nonneg (Real.sqrt_nonneg _)] using h
  refine ⟨fun z => ∑' i, b i * wave (ξ i) z,fun z => ?_⟩
  rw [series_action b ξ hb]
  apply tsum_congr
  intro i
  have hn : Real.sqrt (1+‖ξ i‖^2) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  dsimp [b]
  field_simp [hn]

end
end TransportOkaGrauert.FlatNormalSymbol
