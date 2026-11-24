import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic

/-!
# Schur complement at the velocity boundary

These are algebraic and limiting statements about the Levi matrix in the
geodesic frame. The differential-geometric computation of that matrix is
an input. The boundary parameter is `t = (1-r²)/(1+r²)`.
-/

noncomputable section

namespace TransportOkaGrauert.LeviBoundary

open Filter
open scoped Topology

/-- For the angular weight `h`, the subscripts below name derivatives in the
frame `X,H,V`: for example `hv` denotes `H(Vh)`. -/
structure FrameJet where
  curvature : ℝ
  x : ℝ
  h : ℝ
  xx : ℝ
  hh : ℝ
  vv : ℝ
  hv : ℝ
  xv : ℝ

def horizontal (t : ℝ) (j : FrameJet) : ℝ :=
  j.xx + t ^ 2 * j.hh - (1 - t) * j.curvature

def vertical (t : ℝ) (j : FrameJet) : ℝ :=
  (1 - t ^ 2) / t ^ 2 + j.vv

def mixedJ (t : ℝ) (j : FrameJet) : ℝ :=
  (t⁻¹ - t) * j.x + t * j.hv

def mixedR (t : ℝ) (j : FrameJet) : ℝ :=
  (t ^ 2 - 1) * j.h - j.xv

def schur (t : ℝ) (j : FrameJet) : ℝ :=
  horizontal t j - ((mixedJ t j) ^ 2 + (mixedR t j) ^ 2) / vertical t j

def scaledVertical (t : ℝ) (j : FrameJet) : ℝ :=
  1 - t ^ 2 + t ^ 2 * j.vv

def scaledSchur (t : ℝ) (j : FrameJet) : ℝ :=
  horizontal t j -
    (((1 - t ^ 2) * j.x + t ^ 2 * j.hv) ^ 2 + (t * mixedR t j) ^ 2) / scaledVertical t j

/-- Multiplying the vertical block by `t²` and the mixed entries by `t`
removes the singular coefficients without altering the Schur complement. -/
theorem schur_eq_scaled {t : ℝ} (ht : t ≠ 0) (j : FrameJet) :
    schur t j = scaledSchur t j := by
  have hv : scaledVertical t j = t ^ 2 * vertical t j := by
    unfold scaledVertical vertical
    field_simp
  have hc : (1 - t ^ 2) * j.x + t ^ 2 * j.hv = t * mixedJ t j := by
    unfold mixedJ
    field_simp
  unfold schur scaledSchur
  rw [hv, hc]
  have hn : (t * mixedJ t j) ^ 2 + (t * mixedR t j) ^ 2 =
      t ^ 2 * ((mixedJ t j) ^ 2 + (mixedR t j) ^ 2) := by ring
  rw [hn, mul_div_mul_left _ _ (pow_ne_zero 2 ht)]

/-- Along an arbitrary convergent family of jets, the limiting Schur
complement is `X²h − K − (Xh)²`. Only the terms displayed survive. -/
theorem tendsto_schur {α : Type*} {l : Filter α} {t : α → ℝ} {j : α → FrameJet}
    {a : FrameJet} (ht : Tendsto t l (𝓝 0)) (hn : ∀ᶠ i in l, t i ≠ 0)
    (hk : Tendsto (fun i => (j i).curvature) l (𝓝 a.curvature))
    (hx : Tendsto (fun i => (j i).x) l (𝓝 a.x))
    (hh : Tendsto (fun i => (j i).h) l (𝓝 a.h))
    (hxx : Tendsto (fun i => (j i).xx) l (𝓝 a.xx))
    (hhh : Tendsto (fun i => (j i).hh) l (𝓝 a.hh))
    (hvv : Tendsto (fun i => (j i).vv) l (𝓝 a.vv))
    (hhv : Tendsto (fun i => (j i).hv) l (𝓝 a.hv))
    (hxv : Tendsto (fun i => (j i).xv) l (𝓝 a.xv)) :
    Tendsto (fun i => schur (t i) (j i)) l (𝓝 (a.xx - a.curvature - a.x ^ 2)) := by
  have one := tendsto_const_nhds (f := l) (x := (1 : ℝ))
  have ht2 := ht.pow 2
  have ha : Tendsto (fun i => horizontal (t i) (j i)) l (𝓝 (a.xx - a.curvature)) := by
    simpa [horizontal] using (hxx.add (ht2.mul hhh)).sub ((one.sub ht).mul hk)
  have hb : Tendsto (fun i => scaledVertical (t i) (j i)) l (𝓝 1) := by
    simpa [scaledVertical] using (one.sub ht2).add (ht2.mul hvv)
  have hc : Tendsto (fun i => (1 - t i ^ 2) * (j i).x + t i ^ 2 * (j i).hv) l (𝓝 a.x) := by
    simpa using ((one.sub ht2).mul hx).add (ht2.mul hhv)
  have hd : Tendsto (fun i => t i * mixedR (t i) (j i)) l (𝓝 0) := by
    simpa [mixedR] using ht.mul (((ht2.sub one).mul hh).sub hxv)
  have hs : Tendsto (fun i => scaledSchur (t i) (j i)) l (𝓝 (a.xx - a.curvature - a.x ^ 2)) := by
    simpa [scaledSchur] using ha.sub (((hc.pow 2).add (hd.pow 2)).div hb one_ne_zero)
  exact hs.congr' (hn.mono fun i hi => (schur_eq_scaled hi (j i)).symm)

/-- Substitution of the first and second derivatives of `−log b` for a
base weight. Its vertical derivatives vanish. -/
def baseJet (K b bx bh bxx bhh : ℝ) : FrameJet where
  curvature := K
  x := -bx / b
  h := -bh / b
  xx := -bxx / b + (bx / b) ^ 2
  hh := -bhh / b + (bh / b) ^ 2
  vv := 0
  hv := 0
  xv := 0

/-- The base collar has an exact Schur complement. The last two squares
have nonnegative coefficients for all real `t`. -/
theorem base_schur {t b : ℝ} (ht : t ≠ 0) (hden : 1 - t ^ 2 ≠ 0) (hb : b ≠ 0)
    (K bx bh bxx bhh : ℝ) :
    schur t (baseJet K b bx bh bxx bhh) =
      -(bxx + t ^ 2 * bhh) / b - (1 - t) * K +
      t ^ 2 * (bx / b) ^ 2 + t ^ 4 * (bh / b) ^ 2 := by
  rw [schur_eq_scaled ht]
  simp only [scaledSchur, horizontal, scaledVertical, mixedR, baseJet,
    mul_zero, add_zero, sub_zero]
  field_simp
  ring

end TransportOkaGrauert.LeviBoundary
