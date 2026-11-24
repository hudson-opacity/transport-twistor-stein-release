import TransportOkaGrauert.PencilLifts

/-! Local coordinates at the centre of a curved geodesic pencil. -/

noncomputable section

namespace TransportOkaGrauert.PencilCoordinates

open Complex ChartStein
open scoped ComplexConjugate

/-- The base derivative of the pencil stays invertible on the whole open fibre.
The second function supplies the velocity coordinate, even when both scalar
corrections and the radial frame vary with the base. -/
theorem at_center {W ρ : ℂ → ℂ} {l u : E → ℂ} {a w : ℂ}
    (dW : DifferentiableAt ℝ W a) (dρ : DifferentiableAt ℝ ρ a)
    (dl : DifferentiableAt ℝ l (a,w)) (du : DifferentiableAt ℝ u (a,w))
    (hW : W a = 0) (hinj : Function.Injective (fderiv ℝ W a))
    (hρ : ‖ρ a‖ = 1) (hw : ‖w‖ < 1) :
    let m (x : E) := ρ x.1 * x.2
    let q (x : E) := W x.1 - m x ^ 2 * conj (W x.1)
    let F (x : E) := Complex.exp (l x) * q x
    Function.Bijective (fderiv ℝ (fun x : E => (F x, m x - u x * F x)) (a,w)) := by
  intro m q F
  let p : E := (a,w)
  have h1 := hasFDerivAt_fst (𝕜 := ℝ) (p := p)
  have h2 := hasFDerivAt_snd (𝕜 := ℝ) (p := p)
  have hdW := dW.hasFDerivAt.comp p h1
  have hdρ := dρ.hasFDerivAt.comp p h1
  have hdM := hdρ.mul h2
  have hdC := Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp p hdW
  have hdQ := hdW.sub ((hdM.pow 2).mul hdC)
  have hdE := (Complex.hasDerivAt_exp (l p)).comp_hasFDerivAt p dl.hasFDerivAt
  have hdF := hdE.mul hdQ
  have hdG := hdM.sub (du.hasFDerivAt.mul hdF)
  have dF (v : E) : fderiv ℝ F p v = Complex.exp (l p) *
      FlatScalar.firstIntegral (fderiv ℝ W a v.1) (m p) := by
    rw [show fderiv ℝ F p = _ from hdF.fderiv]
    simp [p,m,FlatScalar.firstIntegral,hW,smul_eq_mul]
  have dfm (v : E) : fderiv ℝ m p v = ρ a * v.2 + w * fderiv ℝ ρ a v.1 := by
    rw [show fderiv ℝ m p = _ from hdM.fderiv]
    simp [p,smul_eq_mul]
  have dG (v : E) : fderiv ℝ (fun x => m x - u x * F x) p v =
      fderiv ℝ m p v - u p * fderiv ℝ F p v := by
    rw [show fderiv ℝ (fun x => m x - u x * F x) p = _ from hdG.fderiv,
      show fderiv ℝ m p = _ from hdM.fderiv, show fderiv ℝ F p = _ from hdF.fderiv]
    simp [p, hW, smul_eq_mul]
  let L := (fderiv ℝ F p).prod (fderiv ℝ (fun x => m x - u x * F x) p)
  have heq : fderiv ℝ (fun x : E => (F x, m x - u x * F x)) p = L := by
    rw [show fderiv ℝ (fun x : E => (F x, m x - u x * F x)) p = _ from (hdF.prodMk hdG).fderiv]
    unfold L
    rw [show fderiv ℝ F p = _ from hdF.fderiv, show fderiv ℝ (fun x => m x - u x * F x) p = _ from hdG.fderiv]
  rw [heq]
  have hμ : ‖m p‖ < 1 := by simpa [m,p,norm_mul,hρ] using hw
  have hρ' : ρ a ≠ 0 := norm_ne_zero_iff.mp (by rw [hρ]; exact one_ne_zero)
  have hi : Function.Injective L := by
    apply LinearMap.ker_eq_bot.mp (show LinearMap.ker L.toLinearMap = ⊥ from ?_)
    apply LinearMap.ker_eq_bot'.mpr
    intro v hv
    have hz : fderiv ℝ F p v = 0 := congrArg Prod.fst hv
    have hh : fderiv ℝ (fun x => m x - u x * F x) p v = 0 := congrArg Prod.snd hv
    have base : v.1 = 0 := by
      rw [dF] at hz
      have hb := (SteinDivisor.firstIntegral_interior_zero_iff _ _ hμ).mp
        ((mul_eq_zero.mp hz).resolve_left (Complex.exp_ne_zero _))
      exact hinj (hb.trans (map_zero _).symm)
    rw [dG, hz, dfm, base] at hh
    have vel : v.2 = 0 := (mul_eq_zero.mp (by simpa using hh : ρ a * v.2 = 0)).resolve_left hρ'
    exact Prod.ext base vel
  exact ⟨hi,LinearMap.injective_iff_surjective.mp (show Function.Injective L.toLinearMap from hi)⟩

end TransportOkaGrauert.PencilCoordinates
