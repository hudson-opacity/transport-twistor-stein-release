import TransportOkaGrauert.ChartStein

namespace TransportOkaGrauert.HyperbolicDisk
noncomputable section
open Complex
open scoped ComplexConjugate

def mob (s w : ℂ) : ℂ := (s+w)/(1+conj s*w)

theorem nonzero {s w : ℂ} (hs : ‖s‖ < 1) (hw : ‖w‖ ≤ 1) : 1 + conj s*w ≠ 0 := by
  have h : ‖conj s*w‖ < 1 := by
    rw [norm_mul,Complex.norm_conj]
    exact (mul_le_mul_of_nonneg_left hw (norm_nonneg s)).trans_lt (by simpa using hs)
  intro he
  have hh : conj s*w = -1 := by linear_combination he
  simp [hh] at h

private theorem normSq_difference (s w : ℂ) :
    normSq (1+conj s*w)-normSq (s+w)=(1-normSq s)*(1-normSq w) := by
  simp [Complex.normSq_apply,Complex.mul_re,Complex.mul_im]
  ring

theorem norm_lt {s w : ℂ} (hs : ‖s‖ < 1) (hw : ‖w‖ < 1) : ‖mob s w‖ < 1 := by
  have hid := normSq_difference s w
  simp only [Complex.normSq_eq_norm_sq] at hid
  have pos := mul_pos (show 0 < 1 - ‖s‖^2 by nlinarith [norm_nonneg s])
    (show 0 < 1 - ‖w‖^2 by nlinarith [norm_nonneg w])
  rw [mob,norm_div,div_lt_one (norm_pos_iff.mpr (nonzero hs hw.le))]
  nlinarith [norm_nonneg (s+w), norm_nonneg (1+conj s*w)]

theorem norm_eq {s w : ℂ} (hs : ‖s‖ < 1) (hw : ‖w‖ = 1) : ‖mob s w‖ = 1 := by
  have hid := normSq_difference s w
  simp only [Complex.normSq_eq_norm_sq,hw,one_pow,sub_self,mul_zero] at hid
  rw [mob,norm_div,div_eq_one_iff_eq (norm_ne_zero_iff.mpr (nonzero hs hw.le))]
  nlinarith [norm_nonneg (s+w), norm_nonneg (1+conj s*w)]

theorem injective_on_disk {s w v : ℂ} (hs : ‖s‖ < 1) (hw : ‖w‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    (he : mob s w = mob s v) : w = v := by
  have hd := (div_eq_div_iff (nonzero hs hw) (nonzero hs hv)).mp he
  have hn : 1 - s * conj s ≠ 0 := by
    rw [Complex.mul_conj, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.ofReal_ne_zero,
      Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg s]
  apply sub_eq_zero.mp
  apply (mul_eq_zero.mp (show (1-s*conj s)*(w-v) = 0 by linear_combination hd)).resolve_left hn
end
end TransportOkaGrauert.HyperbolicDisk
