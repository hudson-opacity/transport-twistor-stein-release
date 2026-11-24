import TransportOkaGrauert.PhysicalSteinArea
import Mathlib.Analysis.Normed.Operator.Prod

/-! # Uniform control of horizontal and vertical complex directions

The real parts of the base and velocity coordinates and their derivatives on
the complex-rotated tangent vector determine all four real components. The
two base components determine the horizontal vector alone.
-/

noncomputable section
namespace TransportOkaGrauert.PhysicalSteinDirections

open Set Metric Filter Complex ChartStein CollarGluing PhysicalStein
open scoped ContDiff Topology

def x : E →L[ℝ] ℝ := reCLM.comp (.fst ℝ ℂ ℂ)
def y : E →L[ℝ] ℝ := reCLM.comp (.snd ℝ ℂ ℂ)
def pair (j : E →L[ℝ] E) (L : E →L[ℝ] ℝ) : E →L[ℝ] ℝ × ℝ := L.prod (L.comp j)

private theorem uniform_lower {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [ProperSpace V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {K : Set E} (hk : IsCompact K)
    (T : E → V →L[ℝ] W) (ct : ContinuousOn T K) (inj : ∀ p ∈ K, ∀ v, T p v = 0 → v = 0) :
    ∃ C > 0, ∀ p ∈ K, ∀ v : V, ‖v‖ ≤ C * ‖T p v‖ := by
  let S := K ×ˢ sphere (0:V) 1
  have cs : IsCompact S := hk.prod (isCompact_sphere _ _)
  have low : ∃ m > 0, ∀ p ∈ K, ∀ u : V, ‖u‖ = 1 → m ≤ ‖T p u‖ := by
    by_cases e : S.Nonempty
    · have c : ContinuousOn (fun k : E × V => ‖T k.1 k.2‖) S :=
        ((ct.comp continuous_fst.continuousOn (fun _ h => h.1)).clm_apply continuous_snd.continuousOn).norm
      obtain ⟨k,kS,min⟩ := cs.exists_isMinOn e c
      have h1 : ‖k.2‖ = 1 := by simpa using kS.2
      have ne : T k.1 k.2 ≠ 0 := fun he => by simp [inj _ kS.1 _ he] at h1
      exact ⟨_,norm_pos_iff.mpr ne,fun p hp u hu => isMinOn_iff.mp min (p,u) ⟨hp,by simpa using hu⟩⟩
    · exact ⟨1,zero_lt_one,fun p hp u hu => (e ⟨(p,u),hp,by simpa using hu⟩).elim⟩
  obtain ⟨m,hm,low⟩ := low
  refine ⟨m⁻¹,inv_pos.mpr hm,?_⟩
  intro p hp v
  by_cases hz : v = 0
  · simp [hz]
  have hv := norm_pos_iff.mpr hz
  have H := low p hp (‖v‖⁻¹ • v) (by simp [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hv.le),hv.ne'])
  rw [map_smul,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hv.le),inv_mul_eq_div] at H
  rw [inv_mul_eq_div,le_div_iff₀ hm]
  simpa [mul_comm] using (le_div_iff₀ hv).mp H

theorem horizontal_zero {σ : ℂ → ℝ} {p : E} (hp : ‖p.2‖ < 1) (v : E)
    (h : pair (J σ p) x v = 0) : v.1 = 0 := by
  have h₁ : v.1.re = 0 := congrArg Prod.fst h
  have h₂ : (J σ p v).1.re = 0 := congrArg Prod.snd h
  by_contra hv
  have pos := (base_area_pos_iff σ hp v).mpr hv
  simp [planeArea,h₁,h₂] at pos

theorem horizontal_part {σ : ℂ → ℝ} {p : E} (hp : ‖p.2‖ < 1) (v : E) :
    (J σ p v).1 = (J σ p (v.1,0)).1 := by
  calc (J σ p v).1 = (J σ p ((v.1,0)+(0,v.2))).1 := by simp
    _ = _ := by rw [map_add,vertical_J σ hp]; simp

private theorem pair_cont {σ : ℂ → ℝ} (hs : ContDiff ℝ ∞ σ) {K : Set E} (inside : K ⊆ domain)
    (L : E →L[ℝ] ℝ) : ContinuousOn (fun p => pair (J σ p) L) K := by
  intro p hp
  have h : ContinuousWithinAt (fun q => L.comp (J σ q)) K p :=
    ((contDiffAt_const (c := L)).clm_comp (J_smooth hs (inside hp).2)).continuousAt.continuousWithinAt
  exact (ContinuousLinearMap.prodₗᵢ ℝ).continuous.continuousAt.comp_continuousWithinAt
    ((continuousWithinAt_const (b := L)).prodMk h)

/-- Both estimates are uniform throughout an arbitrary compact portion of the
open bidisk. Norms on the real pairs are maximum norms. -/
theorem direction_bounds {σ : ℂ → ℝ} (hs : ContDiff ℝ ∞ σ) {K : Set E}
    (hk : IsCompact K) (inside : K ⊆ domain) :
    ∃ C > 0, ∀ p ∈ K, ∀ v : E,
      ‖v.1‖ ≤ C*‖pair (J σ p) x v‖ ∧
      ‖v‖ ≤ C*(‖pair (J σ p) x v‖ + ‖pair (J σ p) y v‖) := by
  let H := fun p => (pair (J σ p) x).comp (ContinuousLinearMap.inl ℝ ℂ ℂ)
  let F := fun p => (pair (J σ p) x).prod (pair (J σ p) y)
  have hH : ContinuousOn H K := (pair_cont hs inside x).clm_comp continuousOn_const
  have hF : ContinuousOn F K := (ContinuousLinearMap.prodₗᵢ ℝ).continuous.comp_continuousOn
    ((pair_cont hs inside x).prodMk (pair_cont hs inside y))
  obtain ⟨B,bp,bd⟩ := uniform_lower hk H hH (fun p hp v eq => horizontal_zero (inside hp).2 (v,0) eq)
  obtain ⟨A,ap,ad⟩ := uniform_lower hk F hF (by
    intro p hp v eq
    have h := horizontal_zero (inside hp).2 v (congrArg Prod.fst eq)
    have vv : v = ((0,v.2):E) := Prod.ext h rfl
    have h₁ : v.2.re = 0 := congrArg (fun a : (ℝ×ℝ)×(ℝ×ℝ) => a.2.1) eq
    have h₂ : (J σ p v).2.re = 0 := congrArg (fun a : (ℝ×ℝ)×(ℝ×ℝ) => a.2.2) eq
    rw [vv,vertical_J σ (inside hp).2] at h₂
    exact Prod.ext h (Complex.ext h₁ (by simpa [Complex.mul_re] using h₂)))
  refine ⟨A+B,add_pos ap bp,?_⟩
  intro p hp v
  let X := pair (J σ p) x v
  let Y := pair (J σ p) y v
  have eq : H p v.1 = X := Prod.ext rfl (congrArg Complex.re (horizontal_part (inside hp).2 v).symm)
  have h₁ := bd p hp v.1
  rw [eq] at h₁
  have h₂ := ad p hp v
  change ‖v‖ ≤ A * max ‖X‖ ‖Y‖ at h₂
  exact ⟨h₁.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg X)),
    h₂.trans (mul_le_mul (by linarith) (max_le (by linarith [norm_nonneg Y]) (by linarith [norm_nonneg X]))
      (le_trans (norm_nonneg X) (le_max_left ..)) (add_nonneg ap.le bp.le))⟩

end TransportOkaGrauert.PhysicalSteinDirections
