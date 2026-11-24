import TransportOkaGrauert.HyperbolicDisk

/-! The arclength and turning identities for a disk automorphism applied to a diameter. -/
namespace TransportOkaGrauert.HyperbolicRayAlgebra
noncomputable section
open Complex HyperbolicDisk
open scoped ComplexConjugate

private theorem unit_mul {v : ℂ} (h : ‖v‖=1) : v * conj v = 1 := by
  simp [Complex.mul_conj, Complex.normSq_eq_norm_sq, h]

theorem speed {s v : ℂ} {u : ℝ} (hv : ‖v‖ = 1) (hd : 1 + conj s * (v * (u : ℂ)) ≠ 0) :
    (((1 - Complex.normSq (mob s (v*(u:ℂ)))) : ℝ) : ℂ) *
      (v * conj (1 + conj s * (v*(u:ℂ))) / (1 + conj s * (v*(u:ℂ)))) =
      v * (1 - s * conj s) * (1 - (u:ℂ)^2) / (1 + conj s * (v*(u:ℂ)))^2 := by
  let N := s + v*(u:ℂ)
  let D := 1 + conj s*(v*(u:ℂ))
  have hD : D ≠ 0 := hd
  have hC : conj D ≠ 0 := (map_ne_zero _).mpr hD
  have hnorm : D*conj D-N*conj N = (1-s*conj s)*(1-(u:ℂ)^2) := by
    dsimp [D,N]
    simp only [map_add,map_mul,map_one,starRingEnd_self_apply,Complex.conj_ofReal]
    linear_combination (s*conj s-1)*(u:ℂ)^2*(unit_mul hv)
  have fac : (1:ℂ)-(N/D)*conj (N/D) = (D*conj D - N*conj N)/(D*conj D) := by
    rw [map_div₀]
    field_simp
  push_cast
  rw [← Complex.mul_conj]
  change (1-(N/D)*conj (N/D))*(v*conj D/D) = v*(1-s*conj s)*(1-(u:ℂ)^2)/D^2
  rw [fac,hnorm]
  field_simp

theorem turn {s v : ℂ} {u : ℝ} (hv : ‖v‖ = 1) (hd : 1 + conj s * (v * (u : ℂ)) ≠ 0) :
    ((conj (mob s (v*(u:ℂ)))) * (v * conj (1 + conj s*(v*(u:ℂ))) / (1 + conj s*(v*(u:ℂ))))).im =
      (1-u^2) * ((conj s*v)/(1+conj s*(v*(u:ℂ)))).im := by
  let D := 1 + conj s*(v*(u:ℂ))
  let N := s+v*(u:ℂ)
  have hD : D ≠ 0 := hd
  have hC : conj D ≠ 0 := (map_ne_zero _).mpr hD
  have hn : conj N*v = conj s*v+(u:ℂ) := by
    dsimp [N]
    simp only [map_add,map_mul,Complex.conj_ofReal]
    linear_combination (u:ℂ)*(unit_mul hv)
  have h : conj (N/D)*(v*conj D/D) = (u:ℂ) + ((1-u^2:ℝ):ℂ)*(conj s*v/D) := by
    calc
      _ = conj N*v/D := by rw [map_div₀]; field_simp
      _ = _ := by
        rw [hn]
        push_cast
        field_simp
        dsimp [D]
        ring
  change (conj (N/D)*(v*conj D/D)).im = _
  rw [h]
  simp only [Complex.add_im, Complex.ofReal_im, zero_add, Complex.mul_im, Complex.ofReal_re, zero_mul, add_zero, D]
end
end TransportOkaGrauert.HyperbolicRayAlgebra
