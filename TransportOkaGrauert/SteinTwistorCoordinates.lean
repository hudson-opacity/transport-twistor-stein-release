import TransportOkaGrauert.ChartStein

/-! # Isothermal transport distribution in Wirtinger notation

Bohr and Paternain, *The transport Oka–Grauert principle for simple surfaces*,
section 4.2, equation (4.14) and Lemma 4.9, use the orthonormal fibre coordinate
μ. The horizontal field below retains both of their vertical Wirtinger terms.
-/
namespace TransportOkaGrauert.SteinTwistorCoordinates
noncomputable section
open ChartStein Complex
open scoped ComplexConjugate

/-- Coordinates of a physical tangent vector in the positive orthonormal frame of
the metric exp(2σ)(dx²+dy²). -/
def fibreCoordinate (σ : ℂ → ℝ) (z v : ℂ) : ℂ := (Real.exp (σ z) : ℂ)*v

theorem fibre_norm (σ : ℂ → ℝ) (z v : ℂ) :
    ‖fibreCoordinate σ z v‖ = Real.exp (σ z)*‖v‖ := by
  rw [fibreCoordinate,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]

theorem unit_fibreCoordinate (σ : ℂ → ℝ) (z : ℂ) (w : Circle) :
    fibreCoordinate σ z ((Real.exp (-σ z) : ℂ)*(w : ℂ)) = w := by
  rw [fibreCoordinate,← mul_assoc,← Complex.ofReal_mul,← Real.exp_add,add_neg_cancel]
  simp

def dz (x y : ℂ) : ℂ := (x-I*y)/2
def dzbar (x y : ℂ) : ℂ := (x+I*y)/2

/-- Expression (4.14) acting on a real differential in the oriented isothermal chart. -/
def xi (σ : ℂ → ℝ) (p : E) (D : E →L[ℝ] ℂ) : ℂ :=
  let sx : ℂ := fderiv ℝ σ p.1 1
  let sy : ℂ := fderiv ℝ σ p.1 I
  (Real.exp (-σ p.1) : ℂ) * (p.2^2 * dz (D (1,0)) (D (I,0)) + dzbar (D (1,0)) (D (I,0)) +
    (p.2^2*dz sx sy-dzbar sx sy) *
    (conj p.2 * dzbar (D (0,1)) (D (0,I)) - p.2 * dz (D (0,1)) (D (0,I))))

/-- The fixed-chart holomorphicity equations are equivalent to annihilating the two published fields. -/
theorem satisfiesCR_iff (σ : ℂ → ℝ) (p : E) (D : E →L[ℝ] ℂ) :
    SatisfiesCR σ p D ↔ dzbar (D (0,1)) (D (0,I)) = 0 ∧ xi σ p D = 0 := by
  have vert {a b : ℂ} : dzbar a b = 0 ↔ b = I*a := by
    unfold dzbar
    rw [div_eq_zero_iff,or_iff_left (by norm_num : (2:ℂ) ≠ 0)]
    constructor
    · intro h
      calc b = -(I*(I*b)) := by simp [← mul_assoc]
           _ = I*a := by rw [eq_neg_of_add_eq_zero_right h]; ring
    · intro h
      simp [h,← mul_assoc]
  rw [vert]
  apply and_congr_right
  intro v
  have v1 : dz (D (0,1)) (D (0,I)) = D (0,1) := by simp [dz,v,← mul_assoc]
  have v0 := vert.mpr v
  unfold xi
  rw [v1,v0,mul_zero,zero_sub,mul_eq_zero,or_iff_right (show (Real.exp (-σ p.1) : ℂ) ≠ 0 by exact_mod_cast (Real.exp_ne_zero _))]
  unfold connectionCoefficient dz dzbar
  constructor <;> intro h
  · linear_combination h/2
  · linear_combination 2*h

end
end TransportOkaGrauert.SteinTwistorCoordinates
