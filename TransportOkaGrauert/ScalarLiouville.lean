import TransportOkaGrauert.ConformalFrame
import Mathlib.MeasureTheory.Integral.DivergenceTheorem

/-! # Liouville integration for the isothermal frame

We integrate in Cartesian base coordinates and one fundamental angle interval.
The horizontal faces cancel by angular periodicity and the four remaining
faces lie outside the support of an interior test function.
-/
noncomputable section
namespace TransportOkaGrauert.ScalarLiouville
open Set Function Complex MeasureTheory ConformalFrame FrameLevi
open scoped ContDiff

abbrev BoxSpace := Fin 3 → ℝ

def lo : BoxSpace := ![-2,-2,-Real.pi]
def hi : BoxSpace := ![2,2,Real.pi]
def box := Icc lo hi

private theorem ordered : lo ≤ hi := by
  intro i
  fin_cases i <;> simp [lo,hi,Real.pi_pos.le]

def coordinate (i : Fin 3) : BoxSpace →L[ℝ] ℝ := ContinuousLinearMap.proj i

def point : BoxSpace →L[ℝ] Chart :=
  (((coordinate 0).smulRight (1:ℂ)) + ((coordinate 1).smulRight I)).prod
    ((coordinate 2).prod 0)

theorem point_apply (x : BoxSpace) : point x = (x 0 • (1:ℂ) + x 1 • I,x 2,0) := rfl

def areaDensity (σ : ℂ → ℝ) (p : Chart) := Real.exp (2*σ p.1)

def integral (σ : ℂ → ℝ) (f : Chart → ℝ) := ∫ x in box, areaDensity σ (point x) * f (point x)

def divergence (F : Fin 3 → BoxSpace → ℝ) (x : BoxSpace) :=
  ∑ i : Fin 3, fderiv ℝ (F i) x (Pi.single i 1)

/-- Any smooth flux with matching opposite faces integrates to zero. -/
theorem zero_boundary_flux (F : Fin 3 → BoxSpace → ℝ) (hF : ∀ i, ContDiff ℝ ∞ (F i))
    (boundary : ∀ (i : Fin 3) (y : Fin 2 → ℝ),
      F i (i.insertNth (hi i) y) = F i (i.insertNth (lo i) y)) :
    ∫ x in box, divergence F x = 0 := by
  have hc : Continuous (divergence F) := by
    unfold divergence
    apply continuous_finset_sum
    intro i _
    exact ((hF i).fderiv_right (m := ∞) (by simp)).continuous.clm_apply continuous_const
  have eq := integral_divergence_of_hasFDerivAt_off_countable' lo hi ordered F
    (fun i => fderiv ℝ (F i)) ∅ countable_empty (fun i => (hF i).continuous.continuousOn)
    (fun x _ i => ((hF i).differentiable (by simp) x).hasFDerivAt) (hc.continuousOn.integrableOn_compact isCompact_Icc)
  change _ = _ at eq
  rw [show (∫ x in box, divergence F x) = _ from eq]
  apply Finset.sum_eq_zero
  intro i _
  rw [show (fun y => F i (i.insertNth (hi i) y)) = (fun y => F i (i.insertNth (lo i) y))
    from funext (boundary i), sub_self]

private theorem point_basis (i : Fin 3) :
    point (Pi.single i 1) = ![((1:ℂ),0,0),(I,0,0),(0,1,0)] i := by
  fin_cases i <;> simp [point_apply]

/-- The conformal factor times the rotating Euclidean frame. -/
def rate (σ : ℂ → ℝ) (v n : ℝ → ℂ) (p : Chart) : Chart :=
  (scale σ p • v p.2.1, scale σ p * fderiv ℝ σ p.1 (n p.2.1),0)

def flux (σ : ℂ → ℝ) (v n : ℝ → ℂ) (g : Chart → ℝ) (i : Fin 3) (x : BoxSpace) : ℝ :=
  let p := point x
  Real.exp (σ p.1) * g p * ![(v p.2.1).re,(v p.2.1).im,fderiv ℝ σ p.1 (n p.2.1)] i

private theorem smooth_flux {σ : ℂ → ℝ} (hs : ContDiff ℝ ∞ σ)
    {v n : ℝ → ℂ} (hv : ContDiff ℝ ∞ v) (hn : ContDiff ℝ ∞ n)
    {g : Chart → ℝ} (hg : ContDiff ℝ ∞ g) (i : Fin 3) : ContDiff ℝ ∞ (flux σ v n g i) := by
  have hg' := hs.fderiv_right (m := ∞) (by simp)
  have hpt : ContDiff ℝ ∞ (fun x : BoxSpace => point x) := point.contDiff
  have hb : ContDiff ℝ ∞ (fun x : BoxSpace => (point x).1) := contDiff_fst.comp hpt
  have ht : ContDiff ℝ ∞ (fun x : BoxSpace => (point x).2.1) := contDiff_fst.comp (contDiff_snd.comp hpt)
  have hw := (hs.comp hb).exp.mul (hg.comp hpt)
  fin_cases i
  · exact hw.mul (reCLM.contDiff.comp (hv.comp ht))
  · exact hw.mul (imCLM.contDiff.comp (hv.comp ht))
  · exact hw.mul ((hg'.comp hb).clm_apply (hn.comp ht))

/-- Divergence of the weighted rotating frame equals the weighted directional
derivative. The rotating normal satisfies `n' = -v` in both canonical frames. -/
theorem divergence_flux {σ : ℂ → ℝ} (hs : ContDiff ℝ ∞ σ)
    {v n : ℝ → ℂ} (hv : ContDiff ℝ ∞ v) (dn : ∀ θ, HasDerivAt n (-v θ) θ)
    {g : Chart → ℝ} (hg : ContDiff ℝ ∞ g) (x : BoxSpace) :
    divergence (flux σ v n g) x = areaDensity σ (point x) * along (rate σ v n) g (point x) := by
  let p := point x
  let D := fderiv ℝ σ p.1
  let G := fderiv ℝ g p
  let a := Real.exp (σ p.1)
  let u := v p.2.1
  let w := n p.2.1
  have dh := (hg.differentiable (by simp) p).hasFDerivAt.comp x point.hasFDerivAt
  let base := (ContinuousLinearMap.fst ℝ ℂ (ℝ × ℝ)).comp point
  let angle := (coordinate 2)
  have dσ := (hs.differentiable (by simp) p.1).hasFDerivAt.comp x base.hasFDerivAt
  have dwt := dσ.exp.mul dh
  have du := (hv.differentiable (by simp) p.2.1).hasFDerivAt.comp x angle.hasFDerivAt
  have dw := (dn p.2.1).hasFDerivAt.comp x angle.hasFDerivAt
  have dD := ((hs.fderiv_right (m := ∞) (by simp)).differentiable (by simp) p.1).hasFDerivAt.comp x base.hasFDerivAt
  have Fre := dwt.mul (reCLM.hasFDerivAt.comp x du)
  have Fim := dwt.mul (imCLM.hasFDerivAt.comp x du)
  have Fa := dwt.mul (dD.clm_apply dw)
  let v₀ : Chart := (1,0,0)
  let v₁ : Chart := (I,0,0)
  let v₂ : Chart := (0,1,0)
  have b₀ : point (Pi.single (0:Fin 3) 1) = v₀ := point_basis 0
  have b₁ : point (Pi.single (1:Fin 3) 1) = v₁ := point_basis 1
  have b₂ : point (Pi.single (2:Fin 3) 1) = v₂ := point_basis 2
  have θ : (point x).2.1 = x 2 := rfl
  have f₀ : fderiv ℝ (flux σ v n g 0) x (Pi.single 0 1) =
      (a * D 1 * g p + a * G v₀) * u.re := by
    rw [show fderiv ℝ (flux σ v n g 0) x = _ from Fre.fderiv]
    simp [base,angle,coordinate,p,v₀,a,u,D,G,b₀,θ]
    ring
  have f₁ : fderiv ℝ (flux σ v n g 1) x (Pi.single 1 1) =
      (a * D I * g p + a * G v₁) * u.im := by
    rw [show fderiv ℝ (flux σ v n g 1) x = _ from Fim.fderiv]
    simp [base,angle,coordinate,p,v₁,a,u,D,G,b₁,θ]
    ring
  have f₂ : fderiv ℝ (flux σ v n g 2) x (Pi.single 2 1) =
      a * G v₂ * D w - a * g p * D u := by
    rw [show fderiv ℝ (flux σ v n g 2) x = _ from Fa.fderiv]
    simp [base,angle,coordinate,p,v₂,a,u,w,D,G,b₂,ContinuousLinearMap.comp_apply,θ]
    ring
  have decomp : u.re • (1:ℂ) + u.im • I = u := by apply Complex.ext <;> simp
  have Du : D u = u.re * D 1 + u.im * D I := by
    calc
      D u = D (u.re • (1:ℂ) + u.im • I) := congrArg D decomp.symm
      _ = _ := by rw [map_add,map_smul,map_smul,smul_eq_mul,smul_eq_mul]
  have rg : rate σ v n p = (scale σ p * u.re) • v₀ + (scale σ p * u.im) • v₁ +
      (scale σ p * D w) • v₂ := by
    change (scale σ p • u,scale σ p * D w,0) = _
    simp [v₀,v₁,v₂,Prod.smul_mk]
    linear_combination ((scale σ p : ℝ) : ℂ) * (Complex.re_add_im u).symm
  have sc : areaDensity σ p * scale σ p = a := by
    rw [areaDensity,scale,← Real.exp_add]
    congr 1
    ring
  rw [divergence,Fin.sum_univ_three,f₀,f₁,f₂,Du]
  change _ = areaDensity σ p * G (rate σ v n p)
  rw [rg]
  simp only [map_add,map_smul,smul_eq_mul]
  linear_combination -(u.re * G v₀ + u.im * G v₁ + D w * G v₂) * sc

def shift (p : Chart) : Chart := p + (0,2*Real.pi,0)

def periodic {E : Type*} (g : Chart → E) := ∀ p, g (shift p) = g p

def zero_exterior (g : Chart → ℝ) := ∀ p, 1 < ‖p.1‖ → g p = 0

private theorem matching {F : Fin 3 → Chart → ℝ} (per : ∀ i, periodic (F i))
    (off : ∀ i, zero_exterior (F i)) (i : Fin 3) (y : Fin 2 → ℝ) :
    F i (point (i.insertNth (hi i) y)) = F i (point (i.insertNth (lo i) y)) := by
  have b₀ (s : ℝ) : (point ((0:Fin 3).insertNth s y)).1.re = s := by simp [point_apply]
  have b₁ (s : ℝ) : (point ((1:Fin 3).insertNth s y)).1.im = s := by simp [point_apply]
  have e₀ (s : ℝ) (h : |s| = 2) : F 0 (point ((0:Fin 3).insertNth s y)) = 0 := by
    apply off
    have v := Complex.abs_re_le_norm (point ((0:Fin 3).insertNth s y)).1
    rw [b₀,h] at v
    linarith
  have e₁ (s : ℝ) (h : |s| = 2) : F 1 (point ((1:Fin 3).insertNth s y)) = 0 := by
    apply off
    have v := Complex.abs_im_le_norm (point ((1:Fin 3).insertNth s y)).1
    rw [b₁,h] at v
    linarith
  fin_cases i
  · exact (e₀ (hi 0) (by norm_num [hi])).trans (e₀ (lo 0) (by norm_num [lo])).symm
  · exact (e₁ (hi 1) (by norm_num [hi])).trans (e₁ (lo 1) (by norm_num [lo])).symm
  · have eq : point ((2:Fin 3).insertNth (hi 2) y) = shift (point ((2:Fin 3).insertNth (lo 2) y)) := by
      change (y 0 • (1:ℂ) + y 1 • I,Real.pi,0) =
        (y 0 • (1:ℂ) + y 1 • I,-Real.pi,0) + (0,2*Real.pi,0)
      simp [Prod.mk_add_mk]
      ring
    exact (congrArg (F 2) eq).trans (per 2 _)

theorem integral_along {σ : ℂ → ℝ} (hs : ContDiff ℝ ∞ σ)
    {v n : ℝ → ℂ} (hv : ContDiff ℝ ∞ v) (hn : ContDiff ℝ ∞ n)
    (dn : ∀ θ, HasDerivAt n (-v θ) θ) (pv : Periodic v (2*Real.pi)) (pn : Periodic n (2*Real.pi))
    {g : Chart → ℝ} (hg : ContDiff ℝ ∞ g) (pg : periodic g) (zg : zero_exterior g) :
    integral σ (along (rate σ v n) g) = 0 := by
  let F (i : Fin 3) (p : Chart) :=
    Real.exp (σ p.1) * g p * ![(v p.2.1).re,(v p.2.1).im,fderiv ℝ σ p.1 (n p.2.1)] i
  have pf (i : Fin 3) : periodic (F i) := by
    intro p
    have b : (shift p).1 = p.1 := by simp [shift]
    have a : (shift p).2.1 = p.2.1+2*Real.pi := rfl
    simp only [F,b,a,pg p,pv _,pn _]
  have zf (i : Fin 3) : zero_exterior (F i) := fun p hp => by simp [F,zg p hp]
  have m := zero_boundary_flux (flux σ v n g) (smooth_flux hs hv hn hg) (matching pf zf)
  simpa only [integral,divergence_flux hs hv dn hg] using m

theorem integral_vertical {σ : ℂ → ℝ} (hs : ContDiff ℝ ∞ σ)
    {g : Chart → ℝ} (hg : ContDiff ℝ ∞ g) (pg : periodic g) (zg : zero_exterior g) :
    integral σ (along V g) = 0 := by
  let F (i : Fin 3) (p : Chart) := if i = 2 then areaDensity σ p * g p else 0
  have pf (i : Fin 3) : periodic (F i) := by
    intro p; have b : (shift p).1 = p.1 := by simp [shift]
    simp only [F,areaDensity,b,pg p]
  have zf (i : Fin 3) : zero_exterior (F i) := fun p hp => by simp [F,zg p hp]
  have sm : ContDiff ℝ ∞ (areaDensity σ) := by unfold areaDensity; fun_prop
  have sf (i : Fin 3) : ContDiff ℝ ∞ (fun x => F i (point x)) := by
    by_cases e : i = 2
    · simpa only [F,if_pos e] using (sm.mul hg).comp point.contDiff
    · simp [F,e,contDiff_const]
  have div (x : BoxSpace) : divergence (fun i x => F i (point x)) x = areaDensity σ (point x) * along V g (point x) := by
    rw [divergence, Fin.sum_univ_three]
    simp only [F,show (0:Fin 3) ≠ 2 by decide,show (1:Fin 3) ≠ 2 by decide,if_false,if_true,
      fderiv_const_apply,ContinuousLinearMap.zero_apply,zero_add]
    let p := point x
    have dg := (hg.differentiable (by simp) p).hasFDerivAt.comp x point.hasFDerivAt
    let base := (ContinuousLinearMap.fst ℝ ℂ (ℝ × ℝ)).comp point
    have dσ := (hs.differentiable (by simp) p.1).hasFDerivAt.comp x base.hasFDerivAt
    have dw := ((dσ.const_mul 2).exp).mul dg
    rw [show fderiv ℝ (fun x => areaDensity σ (point x) * g (point x)) x = _ from dw.fderiv]
    have b₂ : point (Pi.single (2:Fin 3) 1) = (0,1,0) := point_basis 2
    simp [base,b₂,areaDensity,along,V,p]
  have m := zero_boundary_flux (fun i x => F i (point x)) sf (matching pf zf)
  simpa only [integral,div] using m

theorem integral_X {σ : ℂ → ℝ} (hs : ContDiff ℝ ∞ σ) {g : Chart → ℝ}
    (hg : ContDiff ℝ ∞ g) (pg : periodic g) (zg : zero_exterior g) : integral σ (along (X σ) g) = 0 := by
  apply integral_along (v := unit) (n := normal) hs (by unfold unit; fun_prop) (by unfold normal; fun_prop)
  · intro θ
    simpa only [normal,unit,neg_smul,neg_add,neg_neg] using
      (((Real.hasDerivAt_sin θ).neg).smul_const (1:ℂ)).add ((Real.hasDerivAt_cos θ).smul_const I)
  · intro θ; simp [unit,Real.cos_add_two_pi,Real.sin_add_two_pi]
  · intro θ; simp [normal,Real.cos_add_two_pi,Real.sin_add_two_pi]
  · exact hg
  · exact pg
  · exact zg

theorem integral_H {σ : ℂ → ℝ} (hs : ContDiff ℝ ∞ σ) {g : Chart → ℝ}
    (hg : ContDiff ℝ ∞ g) (pg : periodic g) (zg : zero_exterior g) : integral σ (along (H σ) g) = 0 := by
  apply integral_along (v := normal) (n := fun θ => -unit θ) hs (by unfold normal; fun_prop) (by unfold unit; fun_prop)
  · intro θ
    exact ((((Real.hasDerivAt_cos θ).smul_const (1:ℂ)).add ((Real.hasDerivAt_sin θ).smul_const I)).neg)
  · intro θ; simp [normal,Real.cos_add_two_pi,Real.sin_add_two_pi]
  · intro θ; simp [unit,Real.cos_add_two_pi,Real.sin_add_two_pi]
  · exact hg
  · exact pg
  · exact zg

theorem periodic_along (P : Chart → Chart) (pp : periodic P) {g : Chart → ℝ} (pg : periodic g) :
    periodic (along P g) := by
  have e : (fun q => g (q+(0,2*Real.pi,0))) = g := funext pg
  intro p
  have eq : fderiv ℝ g (shift p) = fderiv ℝ g p := by rw [shift,← fderiv_comp_add_right,e]
  simp [along,eq,pp p]

theorem exterior_along (P : Chart → Chart) {g : Chart → ℝ} (zg : zero_exterior g) :
    zero_exterior (along P g) := by
  intro p hp
  have eq : g =ᶠ[nhds p] fun _ => 0 := (continuous_fst.norm.continuousAt.eventually_const_lt hp).mono
    (fun q hq => zg q hq)
  simp [along,eq.fderiv_eq]

theorem periodic_X (σ : ℂ → ℝ) : periodic (X σ) := by
  intro p
  change rate σ unit normal (shift p) = rate σ unit normal p
  simp [rate,scale,unit,normal,shift,Real.cos_add_two_pi,Real.sin_add_two_pi]

theorem periodic_H (σ : ℂ → ℝ) : periodic (H σ) := by
  intro p
  change rate σ normal (fun θ => -unit θ) (shift p) = rate σ normal (fun θ => -unit θ) p
  simp [rate,scale,unit,normal,shift,Real.cos_add_two_pi,Real.sin_add_two_pi]

theorem int_linear {σ : ℂ → ℝ} (hs : Continuous σ) {f g k : Chart → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hk : Continuous k) :
    integral σ (fun p => f p - g p + k p) = integral σ f - integral σ g + integral σ k := by
  let w := fun x => areaDensity σ (point x)
  have cw : Continuous w := by unfold w areaDensity; fun_prop
  have hI {v : Chart → ℝ} (hv : Continuous v) : IntegrableOn (fun x => w x * v (point x)) box :=
    (cw.mul (hv.comp point.continuous)).continuousOn.integrableOn_compact isCompact_Icc
  have eq (x : BoxSpace) : areaDensity σ (point x) * (f (point x)-g (point x)+k (point x)) =
      (w x * f (point x) - w x * g (point x)) + w x * k (point x) := by dsimp [w]; ring
  simp only [integral,eq]
  exact (integral_add ((hI hf).sub (hI hg)) (hI hk)).trans (congrArg (fun t => t + _) (integral_sub (hI hf) (hI hg)))

end TransportOkaGrauert.ScalarLiouville
