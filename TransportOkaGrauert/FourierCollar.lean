import TransportOkaGrauert.SmoothFourierFamily

/-! # Smooth Fourier multipliers in a collar of the velocity circle
A smooth extension of exp(s) from s ≤ 0 acts on frequency n by b(n·s).
Uniform Fourier decay absorbs every factor n from differentiation. -/
namespace TransportOkaGrauert.FourierCollar
noncomputable section
open Complex Metric Set SmoothFourierFamily
open scoped ContDiff Topology
variable {B : Type} [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]

structure Symbol (b : ℝ → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ b
  boundedDerivs : ∀ k : ℕ, ∃ C : ℝ, ∀ t, ‖iteratedDeriv k b t‖ ≤ C

theorem Symbol.bounded {b : ℝ → ℝ} (hb : Symbol b) : ∃ C : ℝ, 0 ≤ C ∧ ∀ t, ‖b t‖ ≤ C := by
  obtain ⟨C,hC⟩ := hb.boundedDerivs 0
  simp only [iteratedDeriv_zero] at hC
  exact ⟨C,(norm_nonneg _).trans (hC 0),hC⟩

theorem Symbol.derivative {b : ℝ → ℝ} (hb : Symbol b) : Symbol (deriv b) :=
  ⟨(show ContDiff ℝ (∞+1) b from hb.smooth).deriv',fun k => by simpa only [← iteratedDeriv_succ'] using hb.boundedDerivs (k+1)⟩

private def term (g : B × ℝ → ℂ) (b : ℝ → ℝ) (l : B →L[ℝ] ℝ) (k n : ℕ) (p : B) :=
  (((n:ℝ)^k) * b ((n:ℝ) * l p)) • coeff g (n:ℤ) p

def series (g : B × ℝ → ℂ) (b : ℝ → ℝ) (l : B →L[ℝ] ℝ) (k : ℕ) (p : B) :=
  ∑' n : ℕ, term g b l k (n+1) p

private theorem term_deriv {g : B × ℝ → ℂ} (hg : ContDiff ℝ ∞ g) {b : ℝ → ℝ} (hb : Symbol b)
    (l : B →L[ℝ] ℝ) (k n : ℕ) (p : B) :
    HasFDerivAt (term g b l k n)
      ((((n:ℝ)^k) * b ((n:ℝ) * l p)) • fderiv ℝ (coeff g n) p +
      ((n:ℝ)^(k+1) * deriv b ((n:ℝ)*l p)) • (l.smulRight (coeff g n p))) p := by
  have d := (hb.smooth.differentiable (by simp) ((n:ℝ)*l p)).hasDerivAt
  have dl := d.comp_hasFDerivAt p (l.hasFDerivAt.const_smul (n:ℝ))
  have dc := ((coeff_smooth hg n).differentiable (by simp) p).hasFDerivAt
  have h := (dl.const_smul ((n:ℝ)^k)).smul dc
  convert h using 1
  ext v
  simp [pow_succ,smul_smul,smul_eq_mul,Complex.real_smul]
  ring

private def decay (n : ℕ) : ℝ := 1/((n+1:ℕ):ℝ)^2
private theorem decay_sum : Summable decay :=
  (summable_nat_add_iff (f := fun n : ℕ => 1/(n:ℝ)^2) 1).mpr
    (Real.summable_one_div_nat_pow.mpr (by decide))

private theorem split_decay {a C : ℝ} {n k : ℕ} (hn : 0 < n) (h : (n:ℝ)^(k+2)*a ≤ C) :
    (n:ℝ)^k*a ≤ C*(1/(n:ℝ)^2) := by
  rw [mul_one_div,le_div_iff₀ (by positivity)]
  simpa only [pow_add,mul_right_comm _ a _] using h

private theorem term_bounds {g : B × ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (hp : PeriodicFamily g)
    {b : ℝ → ℝ} (hb : Symbol b) (l : B →L[ℝ] ℝ) (k : ℕ) (K : Set B) (hK : IsCompact K) :
    ∃ M : ℝ, ∀ n : ℕ, ∀ p ∈ K, ‖term g b l k (n+1) p‖ ≤ M*decay n ∧
      ‖fderiv ℝ (term g b l k (n+1)) p‖ ≤ M*decay n := by
  obtain ⟨A,hA,a⟩ := rapid hg hp K hK (k+2)
  obtain ⟨D,hD,d⟩ := rapid_derivative hg hp K hK (k+2)
  obtain ⟨F,hF,f⟩ := rapid hg hp K hK ((k+1)+2)
  obtain ⟨S,hS,s⟩ := hb.bounded
  obtain ⟨T,hT,t⟩ := hb.derivative.bounded
  refine ⟨S*A + S*D + T*‖l‖*F, fun n p h => ?_⟩
  let N := n+1
  have hN : 0 < N := Nat.succ_pos _
  have dn : 0 ≤ decay n := by unfold decay; positivity
  have aux (j : ℕ) (v x c : ℝ) (hv : 0 ≤ v) (hv' : (N:ℝ)^j*v ≤ c*decay n) :
      ‖(N:ℝ)^j*x‖*v ≤ ‖x‖*(c*decay n) := by
    rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ (N:ℝ)^j)]
    exact (show (N:ℝ)^j*‖x‖*v = ‖x‖*((N:ℝ)^j*v) by ring) ▸
      mul_le_mul_of_nonneg_left hv' (norm_nonneg _)
  have boundV := split_decay hN (a p h N hN)
  have boundD := split_decay hN (d p h N hN)
  have boundF := split_decay hN (f p h N hN)
  constructor
  · change ‖((N:ℝ)^k * b ((N:ℝ)*l p)) • coeff g (N:ℤ) p‖ ≤ _
    rw [norm_smul]
    exact (aux k _ _ A (norm_nonneg _) boundV).trans
      (((mul_le_mul_of_nonneg_right (s _) (mul_nonneg hA dn))).trans (by nlinarith [mul_nonneg (mul_nonneg hS hD) dn,mul_nonneg (mul_nonneg (mul_nonneg hT (norm_nonneg l)) hF) dn]))
  · rw [(term_deriv hg hb l k N p).fderiv]
    apply (norm_add_le ..).trans
    simp only [norm_smul]
    have unit := (ContinuousLinearMap.norm_smulRight_apply l (coeff g (N:ℤ) p)).le
    have u := aux k ‖fderiv ℝ (coeff g (N:ℤ)) p‖ (b ((N:ℝ)*l p)) D (norm_nonneg _) boundD
    have v := aux (k+1) ‖coeff g (N:ℤ) p‖ (deriv b ((N:ℝ)*l p)) F (norm_nonneg _) boundF
    calc
      _ ≤ S*(D*decay n) + ‖((N:ℝ)^(k+1)*deriv b ((N:ℝ)*l p))‖ * (‖l‖*‖coeff g (N:ℤ) p‖) :=
        add_le_add (u.trans (mul_le_mul_of_nonneg_right (s _) (mul_nonneg hD dn)))
          (mul_le_mul_of_nonneg_left unit (norm_nonneg _))
      _ ≤ S*(D*decay n) + ‖l‖*(T*(F*decay n)) := by
        apply add_le_add (le_refl _)
        rw [mul_left_comm]
        exact mul_le_mul_of_nonneg_left (v.trans (mul_le_mul_of_nonneg_right (t _) (mul_nonneg hF dn))) (norm_nonneg _)
      _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg hS hA) dn]

private theorem convergence {g : B × ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (hp : PeriodicFamily g)
    {b : ℝ → ℝ} (hb : Symbol b) (l : B →L[ℝ] ℝ) (k : ℕ) (p : B) :
    Summable (fun n : ℕ => term g b l k (n+1) p) ∧
    Summable (fun n : ℕ => fderiv ℝ (term g b l k (n+1)) p) := by
  obtain ⟨M,h⟩ := term_bounds hg hp hb l k {p} isCompact_singleton
  exact ⟨(decay_sum.mul_left M).of_norm_bounded (fun n => (h n p (mem_singleton p)).1),
    (decay_sum.mul_left M).of_norm_bounded (fun n => (h n p (mem_singleton p)).2)⟩

private theorem series_deriv {g : B × ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (hp : PeriodicFamily g)
    {b : ℝ → ℝ} (hb : Symbol b) (l : B →L[ℝ] ℝ) (k : ℕ) (p : B) :
    HasFDerivAt (series g b l k) (∑' n : ℕ, fderiv ℝ (term g b l k (n+1)) p) p := by
  obtain ⟨M,h⟩ := term_bounds hg hp hb l k (closedBall p 1) (isCompact_closedBall _ _)
  apply hasFDerivAt_tsum_of_isPreconnected (decay_sum.mul_left M) (isOpen_ball (x := p) (ε := 1))
    (convex_ball p 1).isPreconnected
  · exact fun n x _ => (term_deriv hg hb l k (n+1) x).differentiableAt.hasFDerivAt
  · exact fun n x hx => (h n x (ball_subset_closedBall hx)).2
  · exact mem_ball_self one_pos
  · exact (convergence hg hp hb l k p).1
  · exact mem_ball_self one_pos

private theorem series_direction {g : B × ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (hp : PeriodicFamily g)
    {b : ℝ → ℝ} (hb : Symbol b) (l : B →L[ℝ] ℝ) (k : ℕ) (p v : B) :
    fderiv ℝ (series g b l k) p v =
      series (direction g (v,0)) b l k p + l v • series g (deriv b) l (k+1) p := by
  let A := ContinuousLinearMap.apply ℝ ℂ v
  have h := A.map_tsum (convergence hg hp hb l k p).2
  rw [(series_deriv hg hp hb l k p).fderiv]
  change A (∑' n : ℕ, fderiv ℝ (term g b l k (n+1)) p) = _
  rw [h]
  unfold series
  rw [← ((convergence hg hp hb.derivative l (k+1) p).1.tsum_const_smul (l v)),← Summable.tsum_add
    (convergence (partial_smooth hg _) (partial_periodic hp _) hb l k p).1
    ((convergence hg hp hb.derivative l (k+1) p).1.const_smul (l v))]
  apply tsum_congr
  intro n
  rw [(term_deriv hg hb l k (n+1) p).fderiv]
  simp only [A,ContinuousLinearMap.apply_apply,ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply,coeff_direction hg,term,smul_smul,mul_comm (l v)]

/-- The positive-frequency series is jointly smooth even as the radial
parameter crosses zero, for every symbol with bounded derivatives. -/
theorem smooth {g : B × ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (hp : PeriodicFamily g)
    {b : ℝ → ℝ} (hb : Symbol b) (l : B →L[ℝ] ℝ) (k : ℕ) : ContDiff ℝ ∞ (series g b l k) := by
  apply contDiff_infty.mpr
  intro j
  induction j generalizing g b k with
  | zero =>
    exact contDiff_zero.mpr (continuous_iff_continuousAt.mpr fun p => (series_deriv hg hp hb l k p).continuousAt)
  | succ j ih =>
    apply (contDiff_succ_iff_fderiv_apply (n := (j : WithTop ℕ∞))).mpr
    refine ⟨fun p => (series_deriv hg hp hb l k p).differentiableAt,by simp,fun v => ?_⟩
    simp only [series_direction hg hp hb]
    exact (ih (partial_smooth hg _) (partial_periodic hp _) hb k).add
      ((ih hg hp hb.derivative (k+1)).const_smul _)

end
end TransportOkaGrauert.FourierCollar
