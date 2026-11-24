import TransportOkaGrauert.PhysicalSteinArea

/-! # Two real coordinate inequalities for compact Levi positivity -/

namespace TransportOkaGrauert.PhysicalSchurEstimate

/-- A vertical Hessian controls almost-vertical vectors and the square of the
new gradient controls all other vectors. -/
theorem positive {M A B N m c X Y S qx qy : ℝ}
    (Mpos : 0 < M) (Aone : 1 ≤ A) (Bbig : 12*M < B)
    (Nbig : 4*M*A*(2+m⁻¹) < N) (mpos : 0 < m) (cm : m ≤ c) (cA : c ≤ A)
    (xn : 0 ≤ X) (yn : 0 ≤ Y) (ne : 0 < X+Y)
    (triangle : A*X ≤ S+c*Y)
    (lowerx : -(M*X*(X+Y)) ≤ qx) (lowery : -(M*X*(X+Y)) ≤ qy) :
    0 < A*qx + c*qy + B*c*Y^2 + N*S^2 := by
  have ap : 0 < A := zero_lt_one.trans_le Aone
  have cp := mpos.trans_le cm
  have bp : 0 < B := (by positivity : 0 < 12*M).trans Bbig
  have np : 0 < N := (by positivity : 0 < 4*M*A*(2+m⁻¹)).trans Nbig
  have lower : -((A+c)*M*X*(X+Y)) ≤ A*qx+c*qy := by
    nlinarith [mul_le_mul_of_nonneg_left lowerx ap.le,mul_le_mul_of_nonneg_left lowery cp.le]
  by_cases small : A*X ≤ 2*c*Y
  · have xle : X ≤ 2*Y := (mul_le_mul_iff_right₀ ap).mp
      (small.trans (by nlinarith [mul_le_mul_of_nonneg_right cA yn]))
    have yp : 0 < Y := by linarith
    have bound : (A+c)*M*X*(X+Y) ≤ 12*M*c*Y^2 := calc
      _ ≤ (2*A)*M*X*(3*Y) := by gcongr <;> linarith
      _ = 6*M*(A*X)*Y := by ring
      _ ≤ 6*M*(2*c*Y)*Y := by gcongr
      _ = _ := by ring
    nlinarith [mul_lt_mul_of_pos_right Bbig (mul_pos cp (sq_pos_of_pos yp)),mul_nonneg np.le (sq_nonneg S)]
  · have cy : c*Y < S := by linarith
    have sp : 0 < S := (mul_nonneg cp.le yn).trans_lt cy
    have xle : X ≤ 2*S := by nlinarith [mul_le_mul_of_nonneg_right Aone xn]
    have yle : Y ≤ m⁻¹*S := by
      rw [inv_mul_eq_div,le_div_iff₀ mpos]
      nlinarith [mul_le_mul_of_nonneg_right cm yn]
    have sumle : X+Y ≤ (2+m⁻¹)*S := by linarith
    have bound : (A+c)*M*X*(X+Y) ≤ 4*M*A*(2+m⁻¹)*S^2 := calc
      _ ≤ (2*A)*M*(2*S)*((2+m⁻¹)*S) := by gcongr; linarith
      _ = _ := by ring
    nlinarith [mul_lt_mul_of_pos_right Nbig (sq_pos_of_pos sp),mul_nonneg (mul_nonneg bp.le cp.le) (sq_nonneg Y)]

theorem norm_pair_sq (a b : ℝ) : ‖(a,b)‖^2 ≤ a^2+b^2 := by
  rw [Prod.norm_def,Real.norm_eq_abs,Real.norm_eq_abs]
  rcases le_total |a| |b| with h|h
  · rw [max_eq_right h,sq_abs]; linarith [sq_nonneg a]
  · rw [max_eq_left h,sq_abs]; linarith [sq_nonneg b]

end TransportOkaGrauert.PhysicalSchurEstimate
