import TransportOkaGrauert.Fourier
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Geodesic transport in an isothermal chart

For `g = exp(2λ) (dx² + dy²)`, equation (2.1) of Bohr–Paternain writes
the geodesic field in the base coordinate `z = x + iy` and velocity angle.
We take that coordinate expression as the definition and compute its action
using the real Fréchet derivative on the base and the ordinary angular
derivative on the circle.
-/

noncomputable section

namespace TransportOkaGrauert.Isothermal

open Complex Fourier

/-- The vertical field, differentiating the actual rotation action. -/
def vertical (f : ℂ → Circle → ℂ) (z : ℂ) (w : Circle) : ℂ :=
  deriv (fun t : ℝ => f z (w * Circle.exp t)) 0

private theorem hasDerivAt_rotated_mode (a : ℂ) (w : Circle) (k : ℤ) :
    HasDerivAt (fun t : ℝ => a * character k (w * Circle.exp t))
      (a * character k w * ((k : ℂ) * I)) 0 := by
  have hrot (t : ℝ) : a * character k (w * Circle.exp t) =
      (a * character k w) * Complex.exp (((k : ℂ) * I) * (t : ℂ)) := by
    rw [show character k (w * Circle.exp t) =
        character k w * character k (Circle.exp t) by
      simp [character, mul_zpow]]
    rw [character_angle]
    ring_nf
  simp_rw [hrot]
  have hid : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0 := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ)))
  simpa using ((hid.const_mul ((k : ℂ) * I)).cexp.const_mul (a * character k w))

/-- A circle character is an eigenfunction of the vertical derivative. -/
theorem vertical_mode (a : ℂ → ℂ) (z : ℂ) (w : Circle) (k : ℤ) :
    vertical (fun p v => a p * character k v) z w =
      a z * character k w * ((k : ℂ) * I) :=
  (hasDerivAt_rotated_mode (a z) w k).deriv

/-- The coefficient of `∂θ` inside the parentheses in (2.1),
`λ_y cos(θ) - λ_x sin(θ)`. -/
def angularDrift (lam : ℂ → ℝ) (z : ℂ) (w : Circle) : ℝ :=
  fderiv ℝ lam z I * (w : ℂ).re - fderiv ℝ lam z 1 * (w : ℂ).im

/-- The oriented isothermal-coordinate expression for the geodesic field. -/
def geodesicX (lam : ℂ → ℝ) (f : ℂ → Circle → ℂ) (z : ℂ) (w : Circle) : ℂ :=
  (Real.exp (-lam z) : ℂ) * (flatX f z w + (angularDrift lam z w : ℂ) * vertical f z w)

private def driftUp (lam : ℂ → ℝ) (z : ℂ) : ℂ :=
  (fderiv ℝ lam z I : ℂ) / 2 - (fderiv ℝ lam z 1 : ℂ) / (2 * I)

private def driftDown (lam : ℂ → ℝ) (z : ℂ) : ℂ :=
  (fderiv ℝ lam z I : ℂ) / 2 + (fderiv ℝ lam z 1 : ℂ) / (2 * I)

private theorem drift_split (lam : ℂ → ℝ) (z : ℂ) (w : Circle) :
    (angularDrift lam z w : ℂ) = driftUp lam z * character 1 w +
      driftDown lam z * character (-1) w := by
  simp only [angularDrift, driftUp, driftDown, character, zpow_one, zpow_neg_one,
    Complex.ofReal_sub, Complex.ofReal_mul]
  rw [Complex.re_eq_add_conj, Complex.im_eq_sub_conj, ← Circle.coe_inv_eq_conj, Circle.coe_inv]
  ring

/-- Output coefficient in mode `k+1`. -/
def raising (lam : ℂ → ℝ) (a : ℂ → ℂ) (z : ℂ) (k : ℤ) : ℂ :=
  (Real.exp (-lam z) : ℂ) * (fderiv ℝ a z 1 / 2 + fderiv ℝ a z I / (2 * I) +
    driftUp lam z * a z * ((k : ℂ) * I))

/-- Output coefficient in mode `k-1`. -/
def lowering (lam : ℂ → ℝ) (a : ℂ → ℂ) (z : ℂ) (k : ℤ) : ℂ :=
  (Real.exp (-lam z) : ℂ) * (fderiv ℝ a z 1 / 2 - fderiv ℝ a z I / (2 * I) +
    driftDown lam z * a z * ((k : ℂ) * I))

/-- The angular drift from a nonconstant conformal metric changes the two
coefficients, and the only output frequencies are still `k+1` and `k-1`. -/
theorem geodesicX_mode (lam : ℂ → ℝ) (a : ℂ → ℂ) (z : ℂ)
    (ha : DifferentiableAt ℝ a z) (k : ℤ) (w : Circle) :
    geodesicX lam (fun p v => a p * character k v) z w =
      raising lam a z k * character (k + 1) w +
      lowering lam a z k * character (k + (-1)) w := by
  rw [geodesicX, flatX_mode a z ha, vertical_mode, drift_split]
  simp only [raising, lowering, character_add]
  ring

/-- The same frequency bound for a finite sum. -/
theorem geodesicX_sum_modes (lam : ℂ → ℝ) (s : Finset ℤ) (a : ℤ → ℂ → ℂ)
    (z : ℂ) (m : ℤ) (hfreq : ∀ k ∈ s, m ≤ k)
    (hdiff : ∀ k ∈ s, DifferentiableAt ℝ (a k) z) :
    FiniteModes (m - 1)
      (geodesicX lam (fun p w => ∑ k ∈ s, a k p * character k w) z) := by
  let term := fun k : ℤ => geodesicX lam (fun p w => a k p * character k w) z
  have hterm (k : ℤ) (hk : k ∈ s) : FiniteModes (m - 1) (term k) := by
    have hk' := hfreq k hk
    have h := (FiniteModes.mode (k + 1) (show m - 1 ≤ k + 1 by omega)
        (raising lam (a k) z k)).add
      (FiniteModes.mode (k + (-1)) (show m - 1 ≤ k + (-1) by omega)
        (lowering lam (a k) z k))
    convert h using 1
    funext w
    exact geodesicX_mode lam (a k) z (hdiff k hk) k w
  convert FiniteModes.finset_sum s term hterm using 1
  funext w
  simp only [geodesicX, flatX, vertical, Finset.sum_apply, term]
  rw [fderiv_fun_sum (fun k hk => (hdiff k hk).mul_const (character k w))]
  rw [deriv_fun_sum (fun k _ => (hasDerivAt_rotated_mode (a k z) w k).differentiableAt)]
  simp [mul_add, Finset.mul_sum, Finset.sum_add_distrib]

/-- The two coordinate geodesic equations with the Christoffel symbols for
`exp(2λ)(dx²+dy²)`. Here `lx` and `ly` are the partial derivatives of λ. -/
def geodesicEquations (lx ly vx vy ax ay : ℝ) : Prop :=
  ax + lx * vx ^ 2 + 2 * ly * vx * vy - lx * vy ^ 2 = 0 ∧
  ay - ly * vx ^ 2 + 2 * lx * vx * vy + ly * vy ^ 2 = 0

/-- The coordinate geodesic equations force exactly the angular drift in
(2.1). The input `hlam` is the chain rule for λ along the curve,
whose velocity is `exp(-λ) (cos θ, sin θ)`. -/
theorem geodesicEquations_iff_angular_velocity {lamAlong θ : ℝ → ℝ} {t lx ly rate : ℝ}
    (hlam : HasDerivAt lamAlong
      (lx * (Real.exp (-lamAlong t) * Real.cos (θ t)) +
       ly * (Real.exp (-lamAlong t) * Real.sin (θ t))) t)
    (hθ : HasDerivAt θ rate t) :
    geodesicEquations lx ly
      (Real.exp (-lamAlong t) * Real.cos (θ t)) (Real.exp (-lamAlong t) * Real.sin (θ t))
      (deriv (fun s => Real.exp (-lamAlong s) * Real.cos (θ s)) t)
      (deriv (fun s => Real.exp (-lamAlong s) * Real.sin (θ s)) t) ↔
    rate = Real.exp (-lamAlong t) * (ly * Real.cos (θ t) - lx * Real.sin (θ t)) := by
  have hx := (hlam.neg.exp.mul hθ.cos).deriv
  have hy := (hlam.neg.exp.mul hθ.sin).deriv
  simp only [Pi.mul_def, Pi.neg_def] at hx hy
  rw [hx, hy]
  set e := Real.exp (-lamAlong t)
  set c := Real.cos (θ t)
  set s := Real.sin (θ t)
  have he : e ≠ 0 := Real.exp_ne_zero _
  have hunit : s ^ 2 + c ^ 2 = 1 := Real.sin_sq_add_cos_sq _
  unfold geodesicEquations
  constructor
  · rintro ⟨hx, hy⟩
    have h : e * (rate - e * (ly*c - lx*s)) = 0 := by
      linear_combination -s * hx + c * hy - e * (rate - e * (ly*c - lx*s)) * hunit
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left he)
  · rintro rfl
    constructor <;> ring

end TransportOkaGrauert.Isothermal
