import TransportOkaGrauert.SteinMomentBridge

/-! # The scalar Hilbert transform correction on a surface

If an even trace u solves Xu = X_perp a and Xv = X_perp u₀ at a point,
the corrected trace has vanishing transport derivative there and mean
a+v₀. Both conclusions use the same smooth trace. -/
namespace TransportOkaGrauert.ScalarHilbertParametrix
noncomputable section
open Complex Metric Set MeasureTheory Filter
open ScalarGeneralTransport ScalarGeneralReduction ChartCoefficients PencilLifts
open scoped ContDiff ComplexConjugate Topology
local instance : Fact (0 < 2*Real.pi) := ⟨Real.two_pi_pos⟩

def sign (k : ℤ) : ℂ := if 0 < k then I else if k < 0 then -I else 0

private theorem summed (u v : Trace) (hu : ContDiff ℝ ∞ (lifted u)) (hv : ContDiff ℝ ∞ (lifted v)) (z : ℂ) (k : ℤ) :
    coefficient (fun y w => u y w + v y w) k z = coefficient u k z + coefficient v k z := by
  have integ (b : Trace) (sb : ContDiff ℝ ∞ (lifted b)) :=
    (circle_cont sb z).integrable_of_hasCompactSupport (μ := AddCircle.haarAddCircle) (HasCompactSupport.of_compactSpace _)
  exact congrFun (fourierCoeff.add (integ u hu) (integ v hv)) k

private theorem constant (a : ℂ) (k : ℤ) :
    fourierCoeff (fun _ : DiskSeries.Angle => a) k = if k = 0 then a else 0 := by
  have e : (fun _ : DiskSeries.Angle => a) = fun t => a * fourier 0 t := by simp
  rw [e,fourierCoeff.const_mul,fourierCoeff_fourier]
  by_cases h : k = 0
  · subst k; simp
  · simp [h]

/-- Signed Hilbert transform with multiplier +i sgn(k). -/
theorem signed (u : Trace) (hu : ContDiff ℝ ∞ (lifted u)) :
    ∃ h : Trace, ContDiff ℝ ∞ (lifted h) ∧ ∀ z ∈ disk, ∀ k, coefficient h k z = sign k * coefficient u k z := by
  obtain ⟨p,proj⟩ := HardyDisk.projector u hu
  let l : Trace := fun z w => 2 * trace p z w - u z w
  let b : Trace := fun z _ => coefficient u 0 z
  have sl : ContDiff ℝ ∞ (lifted l) := (contDiff_const.mul (trace_smooth p)).sub hu
  have sb : ContDiff ℝ ∞ (lifted b) := (smooth_coefficient hu 0).comp contDiff_fst
  refine ⟨fun z w => I * (l z w - b z w),contDiff_const.mul (sl.sub sb),?_⟩
  intro z hz k
  change fourierCoeff (fun t : DiskSeries.Angle => I * (l z t.toCircle - b z t.toCircle)) k = _
  rw [fourierCoeff.const_mul]
  change I * coefficient (fun y w => l y w - b y w) k z = _
  rw [coeff_sub sl sb]
  have el : coefficient l k z = 2 * coefficient (trace p) k z - coefficient u k z := by
    rw [show l = fun y w => (fun y w => (2:ℂ) * trace p y w) y w - u y w from rfl,
      coeff_sub (contDiff_const.mul (trace_smooth p)) hu]
    unfold coefficient
    rw [fourierCoeff.const_mul]
  rw [el,proj z hz,show coefficient b k z = _ from constant (coefficient u 0 z) k]
  rcases lt_trichotomy k 0 with hk | rfl | hk
  · simp [sign,hk,hk.ne,not_le.mpr hk,not_lt.mpr hk.le]
  · simp [sign]; ring
  · simp [sign,hk,hk.ne',hk.le]; ring

def horizontal (s : ℂ) (a : ℂ → ℂ) (z : ℂ) := (1/2:ℂ)*fderiv ℝ a z 1 + s/(2*I)*fderiv ℝ a z I

/-- The rotated horizontal derivative on a base function, with arclength
speed included. Its projected base direction is i times the unit velocity. -/
def perp (σ : ℂ → ℝ) (a : ℂ → ℂ) (z : ℂ) (w : Circle) : ℂ :=
  (Real.exp (-σ z):ℂ) * fderiv ℝ a z (I*(w:ℂ))

private theorem perp_mode (σ : ℂ → ℝ) (a : ℂ → ℂ) (z : ℂ) (k : ℤ) :
    coefficient (perp σ a) k z =
     (Real.exp (-σ z):ℂ) * (if k = 1 then I*horizontal 1 a z else 0) +
     (Real.exp (-σ z):ℂ) * (if k = -1 then -I*horizontal (-1) a z else 0) := by
  let A := I*horizontal 1 a z
  let B := -I*horizontal (-1) a z
  have form (t : DiskSeries.Angle) : perp σ a z t.toCircle =
      (Real.exp (-σ z):ℂ) * (A*fourier 1 t+B*fourier (-1) t) := by
    let w : Circle := ⟨I*(t.toCircle:ℂ), mem_sphere_zero_iff_norm.mpr (by simp)⟩
    have fp := Fourier.linear_split (fderiv ℝ a z) w
    have iw : ((w:ℂ))⁻¹ = -I * (t.toCircle:ℂ)⁻¹ := by
      change (I*_)⁻¹ = _; rw [mul_inv,Complex.inv_I]
    rw [iw] at fp
    simp only [perp,fourier_neg,fourier_one,← Circle.coe_inv_eq_conj,Circle.coe_inv]
    rw [show I*(t.toCircle:ℂ)=(w:ℂ) from rfl,fp]
    change _ * ((_ + _) * (I*(t.toCircle:ℂ)) + (_ - _) * (-I*(t.toCircle:ℂ)⁻¹)) = _
    dsimp [A,B,horizontal]; ring
  let x (t : DiskSeries.Angle) := A*fourier 1 t
  let y (t : DiskSeries.Angle) := B*fourier (-1) t
  have integ (c : ℂ) (j : ℤ) := (continuous_const.mul (fourier (T := 2*Real.pi) j).continuous :
    Continuous (fun t => c*fourier j t)).integrable_of_hasCompactSupport (μ := AddCircle.haarAddCircle) (HasCompactSupport.of_compactSpace _)
  have ix : Integrable x AddCircle.haarAddCircle := integ A 1
  have iy : Integrable y AddCircle.haarAddCircle := integ B (-1)
  unfold coefficient
  simp_rw [form]
  rw [fourierCoeff.const_mul, show (fun t : DiskSeries.Angle => A*fourier 1 t+B*fourier (-1) t) = x+y from rfl,
    fourierCoeff.add ix iy]
  simp only [Pi.add_apply,x,y,fourierCoeff.const_mul,fourierCoeff_fourier,Pi.single_apply]
  split_ifs <;> simp_all [A,B]

private theorem scale_neighbor {σ : ℂ → ℝ} {u h : Trace} (hu : ContDiff ℝ ∞ (lifted u))
    {z : ℂ} (hz : z ∈ disk) (s : ℂ) (k : ℤ) (c : ℂ)
    (eq : ∀ y ∈ disk, coefficient h k y = c * coefficient u k y) :
    neighbor σ h z s k = c*neighbor σ u z s k := by
  have germ : coefficient h k =ᶠ[𝓝 z] (fun y => c*coefficient u k y) :=
    Filter.mem_of_superset (isOpen_ball.mem_nhds hz) (fun y hy => eq y hy)
  have d := (smooth_coefficient hu k).differentiable (by simp) z
  have dd : fderiv ℝ (coefficient h k) z = c • fderiv ℝ (coefficient u k) z :=
    (show coefficient h k =ᶠ[𝓝 z] (fun y => c*coefficient u k y) from germ).fderiv_eq.trans
      (d.hasFDerivAt.const_mul c).fderiv
  simp [neighbor,dd,eq z hz]; ring

private theorem add_x {σ : ℂ → ℝ} {u v : Trace}
    (hu : ContDiff ℝ ∞ (lifted u)) (hv : ContDiff ℝ ∞ (lifted v)) (z : ℂ) (w : Circle) :
    Isothermal.geodesicX σ (fun y s => u y s + v y s) z w =
      Isothermal.geodesicX σ u z w + Isothermal.geodesicX σ v z w := by
  let p := (z,(w:ℂ).arg)
  have d := hu.differentiable (by simp) p
  have e := hv.differentiable (by simp) p
  have eq := Circle.exp_arg w
  rw [← eq,PathContinuation.geodesicX_eq_chart_derivative _ _ _ _ (d.add e),
    PathContinuation.geodesicX_eq_chart_derivative _ _ _ _ d,PathContinuation.geodesicX_eq_chart_derivative _ _ _ _ e]
  exact congrArg (fun L : GeodesicFlowExtension.State →L[ℝ] ℂ => L (PathContinuation.chartVector σ p))
    ((d.hasFDerivAt.add e.hasFDerivAt).fderiv)

private theorem base_neighbor (σ : ℂ → ℝ) (a : ℂ → ℂ) (z s : ℂ) (k : ℤ) :
    neighbor σ (fun y _ => a y) z s k = if k = 0 then horizontal s a z else 0 := by
  by_cases h : k = 0
  · subst k
    have e : coefficient (fun y _ => a y) 0 = a := funext fun x => by
      simpa [coefficient] using constant (a x) 0
    simp [neighbor,e,horizontal]
  · have e : coefficient (fun y _ => a y) k = fun _ => 0 := funext fun x => by
      simpa [coefficient,h] using constant (a x) k
    simp [neighbor,e,h]

private theorem angular_add (u v : DiskSeries.Angle → ℂ) (hu : Continuous u) (hv : Continuous v) (k : ℤ) :
    fourierCoeff (fun t => u t + v t) k = fourierCoeff u k + fourierCoeff v k :=
  congrFun (fourierCoeff.add (hu.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (hv.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))) k

/-- The transport computation underlying the smoothing-parametrix inversion
formula. The two primitives need only satisfy their source equations where
the resulting trace is to be geodesically invariant. -/
theorem correction (σ : ℂ → ℝ) (a : ℂ → ℂ) (sa : ContDiff ℝ ∞ a) (u v : Trace)
    (su : ContDiff ℝ ∞ (lifted u)) (sv : ContDiff ℝ ∞ (lifted v))
    (gap : ∀ y ∈ disk, coefficient u (-1) y = 0 ∧ coefficient u 1 y = 0) :
    ∃ h : Trace, ContDiff ℝ ∞ (lifted h) ∧ (∀ z ∈ disk, coefficient h 0 z = a z + coefficient v 0 z) ∧
      ∀ z ∈ disk, (∀ w, Isothermal.geodesicX σ u z w = perp σ a z w) →
        (∀ w, Isothermal.geodesicX σ v z w = perp σ (coefficient u 0) z w) →
        ∀ w, Isothermal.geodesicX σ h z w = 0 := by
  obtain ⟨b,sb,mode⟩ := signed u su
  let q : Trace := fun y _ => a y
  have sq : ContDiff ℝ ∞ (lifted q) := sa.comp contDiff_fst
  let d : Trace := fun y w => q y w + b y w
  have sd : ContDiff ℝ ∞ (lifted d) := sq.add sb
  let h : Trace := fun y w => d y w + v y w
  refine ⟨h,sd.add sv,?_,?_⟩
  · intro z hz
    change coefficient (fun y w => d y w+v y w) 0 z = _
    rw [summed d v sd sv]
    change coefficient (fun y w => q y w+b y w) 0 z + _ = _
    rw [summed q b sq sb,mode z hz]
    simp [sign,q,coefficient,constant]
  intro z hz U V
  let e : ℂ := Real.exp (-σ z)
  let Up (k : ℤ) := neighbor σ u z 1 k
  let Um (k : ℤ) := neighbor σ u z (-1) k
  have eqU (k : ℤ) : e * (Up (k-1) + Um (k+1)) =
      e*(if k = 1 then I*horizontal 1 a z else 0) +
      e*(if k = -1 then -I*horizontal (-1) a z else 0) := by
    rw [← perp_mode]
    change (Real.exp (-σ z):ℂ)*(neighbor σ u z 1 (k-1)+neighbor σ u z (-1) (k+1)) = _
    rw [← neighbors su]; simp only [coefficient,U]
  have calcB (k : ℤ) : coefficient (Isothermal.geodesicX σ b) k z =
      e*(sign (k-1)*Up (k-1)+sign (k+1)*Um (k+1)) := by
    rw [neighbors sb,scale_neighbor su hz 1 (k-1) (sign (k-1)) (fun y hy => mode y hy _),
      scale_neighbor su hz (-1) (k+1) (sign (k+1)) (fun y hy => mode y hy _)]
  have eV (k : ℤ) : coefficient (Isothermal.geodesicX σ v) k z = coefficient (perp σ (coefficient u 0)) k z := by
    simp only [coefficient,V]
  have yU : Up 0 = horizontal 1 (coefficient u 0) z := by simp [Up,neighbor,horizontal]
  have yM : Um 0 = horizontal (-1) (coefficient u 0) z := by simp [Um,neighbor,horizontal]
  have gone : Up (-1) = 0 := neighbor_zero hz 1 (-1) (fun y hy => (gap y hy).1)
  have gone' : Um 1 = 0 := neighbor_zero hz (-1) 1 (fun y hy => (gap y hy).2)
  have co (k : ℤ) : coefficient (Isothermal.geodesicX σ h) k z = 0 := by
    have form (w : Circle) : Isothermal.geodesicX σ h z w = (Isothermal.geodesicX σ q z w + Isothermal.geodesicX σ b z w) +
        Isothermal.geodesicX σ v z w := by rw [show h = fun y w => d y w+v y w from rfl,add_x sd sv,
          show d = fun y w => q y w+b y w from rfl,add_x sq sb]
    have expd : coefficient (Isothermal.geodesicX σ h) k z =
        coefficient (Isothermal.geodesicX σ q) k z + coefficient (Isothermal.geodesicX σ b) k z +
        coefficient (Isothermal.geodesicX σ v) k z := by
      unfold coefficient
      simp_rw [form]
      rw [angular_add (fun t => Isothermal.geodesicX σ q z t.toCircle + Isothermal.geodesicX σ b z t.toCircle) _ ((geodesic_cont sq σ z).add (geodesic_cont sb σ z)) (geodesic_cont sv σ z),
        angular_add _ _ (geodesic_cont sq σ z) (geodesic_cont sb σ z)]
    rw [expd,neighbors sq,show q = (fun y _ => a y) from rfl,base_neighbor,base_neighbor,calcB,eV,perp_mode]
    change e * _ + e * _ + (e * _ + e * _) = 0
    have en : e ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
    have relation := mul_left_cancel₀ en (show e*(Up (k-1)+Um (k+1)) =
      e*((if k = 1 then I*horizontal 1 a z else 0) + (if k = -1 then -I*horizontal (-1) a z else 0)) from (eqU k).trans (mul_add e _ _).symm)
    rw [← mul_add,← mul_add,← mul_add]
    apply mul_eq_zero_of_right
    by_cases kp : k = 1
    · subst k
      norm_num [sign,yU] at relation ⊢
      linear_combination (norm := (ring_nf; simp [Complex.I_sq])) I * relation
    by_cases km : k = -1
    · subst k
      norm_num [sign,yM] at relation ⊢
      linear_combination (norm := (ring_nf; simp [Complex.I_sq])) -I * relation
    by_cases kz : k = 0
    · subst k
      norm_num [sign,gone,gone']
    rcases lt_or_gt_of_ne kz with hn|hp
    · have i : k-1 < 0 := by omega
      have j : k+1 < 0 := by omega
      have sig {m : ℤ} (hs : m < 0) : sign m = -I := by rw [sign,if_neg (not_lt.mpr hs.le),if_pos hs]
      simp only [if_neg kp,if_neg km,if_neg i.ne,if_neg j.ne,zero_add,add_zero,sig i,sig j] at relation ⊢
      linear_combination -I * relation
    · have i : 0 < k-1 := by omega
      have j : 0 < k+1 := by omega
      have sig {m : ℤ} (hs : 0 < m) : sign m = I := if_pos hs
      simp only [if_neg kp,if_neg km,if_neg i.ne',if_neg j.ne',zero_add,add_zero,sig i,sig j] at relation ⊢
      linear_combination I * relation
  have sh : ContDiff ℝ ∞ (lifted h) := sd.add sv
  have equal := CoefficientBridge.eq_of_coeff_eq (geodesic_cont sh σ z)
    (g := fun _ => (0:ℂ)) continuous_const (fun k => by simpa [constant] using co k)
  intro w
  let t : DiskSeries.Angle := ((w:ℂ).arg : ℝ)
  have rel : t.toCircle = w := (ChartModes.toCircle_angle _).trans (Circle.exp_arg w)
  simpa only [rel] using congrFun equal t

end
end TransportOkaGrauert.ScalarHilbertParametrix
