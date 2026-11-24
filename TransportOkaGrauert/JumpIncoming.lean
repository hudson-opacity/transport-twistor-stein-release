import TransportOkaGrauert.JumpingLines

/-! The incoming trace of the Euclidean jumping-line example and its
reconstruction along the chords of the closed unit disk. -/

noncomputable section

namespace TransportOkaGrauert.JumpIncoming

open scoped ComplexConjugate
open JumpingLines

/-- Euclidean dot product of the base vector with the unit velocity. At a
boundary point the base vector is the outward unit normal. -/
def normalDot (z : ℂ) (v : Circle) : ℝ := (z * conj (v : ℂ)).re

def discriminant (z : ℂ) (v : Circle) : ℝ := normalDot z v ^ 2 + (1 - ‖z‖ ^ 2)

/-- Distance travelled backwards to the incoming endpoint of the chord. -/
def backwardTime (z : ℂ) (v : Circle) : ℝ :=
  normalDot z v + Real.sqrt (discriminant z v)

def entry (z : ℂ) (v : Circle) : ℂ := z - (backwardTime z v : ℂ) * v

private theorem unit_conj (v : Circle) : (v : ℂ) * conj (v : ℂ) = 1 := by
  rw [← Circle.coe_inv_eq_conj, Circle.coe_inv, mul_inv_cancel₀ v.coe_ne_zero]

private theorem dot_retreat (z : ℂ) (v : Circle) (t : ℝ) :
    normalDot (z - (t : ℂ) * v) v = normalDot z v - t := by
  simp [normalDot, sub_mul, mul_assoc, unit_conj]

private theorem norm_sq_retreat (z : ℂ) (v : Circle) (t : ℝ) :
    ‖z - (t : ℂ) * v‖ ^ 2 = ‖z‖ ^ 2 + t ^ 2 - 2 * t * normalDot z v := by
  have hnorm : ‖(t : ℂ) * v‖ ^ 2 = t ^ 2 := by
    simp [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hprod : z * conj ((t : ℂ) * (v : ℂ)) = (t : ℂ) * (z * conj (v : ℂ)) := by
    simp [mul_left_comm]
  rw [Complex.sq_norm, Complex.normSq_sub, Complex.normSq_eq_norm_sq,
    Complex.normSq_eq_norm_sq, hnorm, hprod]
  simp [normalDot, Complex.mul_re]
  ring

theorem discriminant_nonneg {z : ℂ} (hz : ‖z‖ ≤ 1) (v : Circle) :
    0 ≤ discriminant z v := by
  unfold discriminant
  nlinarith [sq_nonneg (normalDot z v), norm_nonneg z, mul_self_le_mul_self (norm_nonneg z) hz]

theorem backwardTime_nonneg {z : ℂ} (hz : ‖z‖ ≤ 1) (v : Circle) :
    0 ≤ backwardTime z v := by
  have hr := Real.sq_sqrt (discriminant_nonneg hz v)
  have hpos := Real.sqrt_nonneg (discriminant z v)
  have hs : normalDot z v ^ 2 ≤ discriminant z v := by
    unfold discriminant
    nlinarith [mul_self_le_mul_self (norm_nonneg z) hz]
  unfold backwardTime
  nlinarith [sq_nonneg (normalDot z v + Real.sqrt (discriminant z v))]

theorem entry_norm {z : ℂ} (hz : ‖z‖ ≤ 1) (v : Circle) : ‖entry z v‖ = 1 := by
  have hr := Real.sq_sqrt (discriminant_nonneg hz v)
  have he : ‖entry z v‖ ^ 2 = 1 := by
    rw [entry, norm_sq_retreat, backwardTime]
    unfold discriminant at hr ⊢
    nlinarith
  nlinarith [norm_nonneg (entry z v)]

theorem entry_inward (z : ℂ) (v : Circle) : normalDot (entry z v) v ≤ 0 := by
  rw [entry, dot_retreat, backwardTime]
  linarith [Real.sqrt_nonneg (discriminant z v)]

/-- The unit-boundary equation has at most one root whose velocity is
incoming. This singles out the plus sign in the formula for backward travel. -/
theorem backwardTime_unique {z : ℂ} (v : Circle) {t : ℝ}
    (hb : ‖z - (t : ℂ) * v‖ = 1) (hi : normalDot (z - (t : ℂ) * v) v ≤ 0) :
    t = backwardTime z v := by
  rw [dot_retreat] at hi
  have hn := norm_sq_retreat z v t
  rw [hb] at hn
  have hs : discriminant z v = (t - normalDot z v) ^ 2 := by
    unfold discriminant
    nlinarith
  have hp : 0 ≤ t - normalDot z v := by linarith
  rw [backwardTime, hs, Real.sqrt_sq_eq_abs, abs_of_nonneg hp]
  ring

/-- The incoming unit tangent boundary, including its glancing directions. -/
structure Incoming where
  point : ℂ
  velocity : Circle
  onBoundary : ‖point‖ = 1
  inward : normalDot point velocity ≤ 0

def incomingState (z : ℂ) (hz : ‖z‖ ≤ 1) (v : Circle) : Incoming :=
  ⟨entry z v, v, entry_norm hz v, entry_inward z v⟩

def traceW (s : Incoming) : Mat := W s.point s.velocity

/-- The trace on the incoming boundary determines the original matrix first
integral throughout the closed unit disk. -/
theorem reconstruct (z : ℂ) (hz : ‖z‖ ≤ 1) (v : Circle) :
    traceW (incomingState z hz v) = W z v := by
  simpa [traceW, incomingState, entry, sub_eq_add_neg] using W_advance z v (-backwardTime z v)

/-- Among chord-invariant matrix fields on the disk, the incoming boundary
values determine the example uniquely. -/
theorem unique_extension (U : ℂ → Circle → Mat)
    (hchord : ∀ (z : ℂ) (v : Circle) (t : ℝ), ‖z‖ ≤ 1 → ‖z + (t : ℂ) * v‖ ≤ 1 →
      U (z + (t : ℂ) * v) v = U z v)
    (htrace : ∀ s : Incoming, U s.point s.velocity = traceW s)
    (z : ℂ) (hz : ‖z‖ ≤ 1) (v : Circle) : U z v = W z v := by
  have hentry : U (entry z v) v = U z v := by
    have he := (entry_norm hz v).le
    simp only [entry, sub_eq_add_neg, ← neg_mul, ← Complex.ofReal_neg] at he ⊢
    exact hchord z v (-backwardTime z v) hz he
  calc
    U z v = U (entry z v) v := hentry.symm
    _ = traceW (incomingState z hz v) := htrace (incomingState z hz v)
    _ = W z v := reconstruct z hz v

/-- Backward travel fixes each incoming state, including tangencies. -/
theorem backwardTime_incoming (s : Incoming) : backwardTime s.point s.velocity = 0 := by
  simp [backwardTime, discriminant, s.onBoundary, Real.sqrt_sq_eq_abs, abs_of_nonpos s.inward]

theorem entry_incoming (s : Incoming) : entry s.point s.velocity = s.point := by
  simp [entry, backwardTime_incoming]

/-- The other endpoint of a chord through a boundary state. Travel along the
velocity from an incoming state takes time minus twice the outward dot product. -/
def oppositePoint (z : ℂ) (v : Circle) : ℂ :=
  z - ((2 * normalDot z v : ℝ) : ℂ) * v

theorem normalDot_opposite (z : ℂ) (v : Circle) :
    normalDot (oppositePoint z v) v = -normalDot z v := by
  rw [oppositePoint, dot_retreat]
  ring

theorem opposite_boundary {z : ℂ} (hz : ‖z‖ = 1) (v : Circle) :
    ‖oppositePoint z v‖ = 1 := by
  have h : ‖oppositePoint z v‖ ^ 2 = 1 := by
    rw [oppositePoint, norm_sq_retreat, hz]
    ring
  nlinarith [norm_nonneg (oppositePoint z v)]

theorem opposite_outgoing (s : Incoming) :
    0 ≤ normalDot (oppositePoint s.point s.velocity) s.velocity := by
  rw [normalDot_opposite]
  exact neg_nonneg.mpr s.inward

theorem opposite_involution (z : ℂ) (v : Circle) :
    oppositePoint (oppositePoint z v) v = z := by
  change oppositePoint z v - ((2 * normalDot (oppositePoint z v) v : ℝ) : ℂ) * v = z
  rw [normalDot_opposite, oppositePoint]
  push_cast
  ring

/-- Scattering compatibility of the full smooth boundary matrix: its incoming
and outgoing values agree at the two ends of each chord. -/
theorem scattering_compatibility (s : Incoming) :
    W (oppositePoint s.point s.velocity) s.velocity = traceW s := by
  simpa [traceW, oppositePoint, sub_eq_add_neg] using
    W_advance s.point s.velocity (-(2 * normalDot s.point s.velocity))

/-- On the outgoing boundary the incoming-footpoint construction is precisely
the chord scattering relation, including chords of zero length. -/
theorem entry_from_exit (s : Incoming) :
    entry (oppositePoint s.point s.velocity) s.velocity = s.point := by
  have hz := opposite_boundary s.onBoundary s.velocity
  have hp := opposite_outgoing s
  have ht : backwardTime (oppositePoint s.point s.velocity) s.velocity =
      2 * normalDot (oppositePoint s.point s.velocity) s.velocity := by
    simp [backwardTime, discriminant, hz, Real.sqrt_sq_eq_abs, abs_of_nonneg hp, two_mul]
  rw [entry, ht]
  exact opposite_involution s.point s.velocity

end TransportOkaGrauert.JumpIncoming
