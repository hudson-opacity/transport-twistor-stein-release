import TransportOkaGrauert.HyperbolicCR

/-! A holomorphic pencil for the hyperbolic model, including its transverse zero
and the full two-complex-dimensional coordinate differential at its centre. -/

noncomputable section

namespace TransportOkaGrauert.HyperbolicPencil

open Complex ChartStein HyperbolicCR
open Filter
open scoped ComplexConjugate ContDiff Topology

def divisor (c : ℝ) (a : ℂ) (p : E) : ℂ :=
  let t := (c:ℂ)*a
  let A := endpoint c 1 p
  let B := endpoint c (-1) p
  (A-t)*(1-conj t*B) + (B-t)*(1-conj t*A)

private def rad (c : ℝ) (a z : ℂ) : ℂ :=
  ((c:ℂ)*z - (c:ℂ)*a) * (1 - conj ((c:ℂ)*a)*((c:ℂ)*z))

private def den (c : ℝ) (p : E) : ℂ := 1 - (conj ((c:ℂ)*p.1) * p.2)^2

private theorem reduce (s t w : ℂ) (hp : 1+conj s*w ≠ 0) (hm : 1-conj s*w ≠ 0) :
    let A := (s+w)/(1+conj s*w)
    let B := (s-w)/(1-conj s*w)
    (A-t)*(1-conj t*B) + (B-t)*(1-conj t*A) =
      2*FlatScalar.firstIntegral ((s-t)*(1-conj t*s)) w/(1-(conj s*w)^2) := by
  intro A B
  let P := 1+conj s*w
  let M := 1-conj s*w
  have ha : A*P = s+w := div_mul_cancel₀ _ hp
  have hb : B*M = s-w := div_mul_cancel₀ _ hm
  have hn : 1-(conj s*w)^2 = P*M := by dsimp [P,M]; ring
  rw [hn]
  apply (eq_div_iff (mul_ne_zero hp hm)).mpr
  calc
    _ = (A*P-t*P)*(M-conj t*(B*M))+(B*M-t*M)*(P-conj t*(A*P)) := by ring
    _ = _ := by
      rw [ha,hb]
      simp only [P,M,FlatScalar.firstIntegral,map_mul,map_sub,map_one,starRingEnd_self_apply]
      ring

theorem divisor_eq (c : ℝ) (a : ℂ) (p : E) (hplus : 1+conj ((c:ℂ)*p.1)*p.2 ≠ 0)
    (hminus : 1-conj ((c:ℂ)*p.1)*p.2 ≠ 0) :
    divisor c a p = 2*FlatScalar.firstIntegral
      (((c:ℂ)*p.1-(c:ℂ)*a)*(1-conj ((c:ℂ)*a)*((c:ℂ)*p.1))) p.2 /
      (1-(conj ((c:ℂ)*p.1)*p.2)^2) := by
  simpa [divisor,endpoint,sub_eq_add_neg] using reduce ((c:ℂ)*p.1) ((c:ℂ)*a) p.2 hplus hminus

private theorem small {c : ℝ} (hc : 0<c) (h1 : c<1) {z : ℂ} (hz : ‖z‖≤1) :
    ‖(c:ℂ)*z‖ < 1 := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
  exact (mul_le_of_le_one_right hc.le hz).trans_lt h1

private theorem factors {c : ℝ} {z w : ℂ} (hc : 0<c) (h1 : c<1) (hz : ‖z‖≤1) (hw : ‖w‖≤1) :
    1+conj ((c:ℂ)*z)*w ≠ 0 ∧ 1-conj ((c:ℂ)*z)*w ≠ 0 := by
  constructor
  · simpa using denom_ne (p := (z,w)) hc h1 (Or.inl rfl : (1:ℝ)=1 ∨ (1:ℝ) = -1) hz hw
  · simpa [sub_eq_add_neg] using denom_ne (p := (z,w)) hc h1 (Or.inr rfl : (-1:ℝ)=1 ∨ (-1:ℝ) = -1) hz hw

private theorem den_ne {c : ℝ} {z w : ℂ} (hc : 0<c) (h1 : c<1) (hz : ‖z‖≤1) (hw : ‖w‖≤1) :
    den c (z,w) ≠ 0 := by
  obtain ⟨hp,hm⟩ := factors hc h1 hz hw
  convert mul_ne_zero hp hm using 1
  unfold den
  ring

theorem zero_iff {c : ℝ} {a z w : ℂ} (hc : 0<c) (h1 : c<1) (ha : ‖a‖≤1)
    (hz : ‖z‖≤1) (hw : ‖w‖<1) : divisor c a (z,w)=0 ↔ z=a := by
  obtain ⟨hp,hm⟩ := factors hc h1 hz hw.le
  rw [divisor_eq c a (z,w) hp hm]
  have hn := den_ne hc h1 hz hw.le
  have hfac : 1-conj ((c:ℂ)*a)*((c:ℂ)*z) ≠ 0 := (factors hc h1 ha (small hc h1 hz).le).2
  have hc' : (c:ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  change 2 * FlatScalar.firstIntegral (rad c a z) w / den c (z,w) = 0 ↔ _
  simp only [div_eq_zero_iff, or_iff_left hn, mul_eq_zero, OfNat.ofNat_ne_zero,
    false_or, SteinDivisor.firstIntegral_interior_zero_iff _ _ hw, rad,
    sub_eq_zero, mul_right_inj' hc', or_iff_left (sub_ne_zero.mp hfac)]

theorem at_centre {c : ℝ} {a w : ℂ} (hc : 0<c) (h1 : c<1) (ha : ‖a‖≤1)
    (hw : ‖w‖≤1) : divisor c a (a,w)=0 := by
  obtain ⟨hp,hm⟩ := factors hc h1 ha hw
  rw [divisor_eq c a (a,w) hp hm]
  simp [FlatScalar.firstIntegral]

private theorem rad_deriv (c : ℝ) (a : ℂ) : HasDerivAt (rad c a)
    ((c:ℂ)*(1-conj ((c:ℂ)*a)*((c:ℂ)*a))) a := by
  have hd := (((hasDerivAt_id a).const_mul (c:ℂ)).sub_const ((c:ℂ)*a)).mul
    ((hasDerivAt_const a (1:ℂ)).sub (((hasDerivAt_id a).const_mul (c:ℂ)).const_mul (conj ((c:ℂ)*a))))
  convert hd using 1
  · simp

private theorem fibre_deriv {c : ℝ} {a w : ℂ} (hp : 1+conj ((c:ℂ)*a)*w ≠ 0) :
    HasDerivAt (fun v => endpoint c 1 (a,v))
      ((1-conj ((c:ℂ)*a)*((c:ℂ)*a))/(1+conj ((c:ℂ)*a)*w)^2) w := by
  have hd := ((hasDerivAt_const w ((c:ℂ)*a)).add (hasDerivAt_id w)).div
    ((hasDerivAt_const w (1:ℂ)).add ((hasDerivAt_id w).const_mul (conj ((c:ℂ)*a)))) hp
  convert hd using 1
  · funext v; simp [endpoint]
  · simp; ring

/-- The divisor and the positive endpoint give real-invertible local holomorphic
coordinates at every interior velocity over the centre of the pencil. -/
theorem coordinates {c : ℝ} {a w : ℂ} (hc : 0<c) (h1 : c<1) (ha : ‖a‖≤1) (hw : ‖w‖<1) :
    Function.Bijective (fderiv ℝ (fun x : E => (divisor c a x,endpoint c 1 x)) (a,w)) := by
  let p : E := (a,w)
  let s : ℂ := (c:ℂ)*a
  let K : ℂ := (c:ℂ)*(1-conj s*s)
  let g (x : E) := 2/den c x
  let q (x : E) := FlatScalar.firstIntegral (rad c a x.1) x.2
  have hp := (factors hc h1 ha hw.le).1
  have hm := (factors hc h1 ha hw.le).2
  have hd := den_ne hc h1 ha hw.le
  have hK₁ : 1-conj s*s ≠ 0 := (factors hc h1 ha (small hc h1 ha).le).2
  have hK : K ≠ 0 := mul_ne_zero (by exact_mod_cast hc.ne') hK₁
  have hlocal : divisor c a =ᶠ[𝓝 p] fun y => g y * q y := by
    have ha' : ContinuousAt (fun y : E => 1+conj ((c:ℂ)*y.1)*y.2) p := by fun_prop
    have hb' : ContinuousAt (fun y : E => 1-conj ((c:ℂ)*y.1)*y.2) p := by fun_prop
    filter_upwards [ha'.eventually_ne (show 1+conj ((c:ℂ)*p.1)*p.2 ≠ 0 from hp),
      hb'.eventually_ne (show 1-conj ((c:ℂ)*p.1)*p.2 ≠ 0 from hm)] with y hy hy'
    rw [divisor_eq c a y hy hy']
    dsimp only [g,q,rad,den]
    rw [div_eq_mul_inv,div_eq_mul_inv]
    ring
  have hdg : DifferentiableAt ℝ g p := by
    have hden : DifferentiableAt ℝ (den c) p := by
      have hbar : DifferentiableAt ℝ (fun y : E => conj ((c:ℂ)*y.1)) p :=
        Complex.conjCLE.differentiableAt.comp p ((differentiableAt_const (c:ℂ)).mul differentiableAt_fst)
      exact (differentiableAt_const _).sub ((hbar.mul differentiableAt_snd).pow 2)
    have hinv := (contDiffAt_inv ℝ hd).differentiableAt (n := 1) (by decide)
    simpa only [g,div_eq_mul_inv] using
      (differentiableAt_const (𝕜 := ℝ) (2:ℂ)).mul (hinv.comp p hden)
  have hr := (rad_deriv c a).hasFDerivAt.restrictScalars ℝ
  have hb := hr.comp p (hasFDerivAt_fst (𝕜 := ℝ) (p := p))
  have hdq := hb.sub (((hasFDerivAt_snd (𝕜 := ℝ) (p := p)).pow 2).mul
    (Complex.conjCLE.hasFDerivAt.comp p hb))
  have hdf := (hdg.hasFDerivAt.mul hdq).congr_of_eventuallyEq hlocal
  have slopeF (v : E) :
      fderiv ℝ (divisor c a) p v = g p * FlatScalar.firstIntegral (K*v.1) w := by
    rw [hdf.fderiv]
    simp [FlatScalar.firstIntegral,rad,p,K,s,smul_eq_mul, mul_comm]
  have hdG : DifferentiableAt ℝ (endpoint c 1) p := by
    have h' : 1+conj ((c:ℂ)*p.1)*(1:ℝ)*p.2 ≠ 0 := by simpa [p] using hp
    exact (endpoint_smooth c 1 p h').differentiableAt (by simp)
  have slopeG (b : ℂ) : fderiv ℝ (endpoint c 1) p (0,b) =
      ((1-conj s*s)/(1+conj s*w)^2)*b := by
    have hh := hdG.hasFDerivAt.comp w ((hasFDerivAt_const a w).prodMk (hasFDerivAt_id w))
    have hh' := (fibre_deriv (c := c) (a := a) (w := w) hp).hasFDerivAt.restrictScalars ℝ
    have ha' := congrArg (fun D : ℂ →L[ℝ] ℂ => D b) (hh.fderiv.symm.trans hh'.fderiv)
    simpa [s,mul_comm,smul_eq_mul] using ha'
  let L := (fderiv ℝ (divisor c a) p).prod (fderiv ℝ (endpoint c 1) p)
  rw [show fderiv ℝ (fun x : E => (divisor c a x,endpoint c 1 x)) p = L from
    (hdf.differentiableAt.hasFDerivAt.prodMk hdG.hasFDerivAt).fderiv]
  have hi : Function.Injective L := by
    apply LinearMap.ker_eq_bot.mp (show LinearMap.ker L.toLinearMap = ⊥ from ?_)
    apply LinearMap.ker_eq_bot'.mpr
    intro v hv
    have hz : fderiv ℝ (divisor c a) p v = 0 := congrArg Prod.fst hv
    have hh : fderiv ℝ (endpoint c 1) p v = 0 := congrArg Prod.snd hv
    have hgp : g p ≠ 0 := div_ne_zero (by norm_num) hd
    rw [slopeF] at hz
    have hbase := (SteinDivisor.firstIntegral_interior_zero_iff _ _ hw).mp ((mul_eq_zero.mp hz).resolve_left hgp)
    have hbase' := (mul_eq_zero.mp hbase).resolve_left hK
    have heq : v = (0,v.2) := Prod.ext hbase' rfl
    rw [heq,slopeG] at hh
    exact Prod.ext hbase' ((mul_eq_zero.mp hh).resolve_left (div_ne_zero hK₁ (pow_ne_zero 2 hp)))
  exact ⟨hi, LinearMap.injective_iff_surjective.mp (show Function.Injective L.toLinearMap from hi)⟩

end TransportOkaGrauert.HyperbolicPencil
