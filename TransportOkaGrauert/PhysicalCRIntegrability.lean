import TransportOkaGrauert.PhysicalStein
import TransportOkaGrauert.ChartCorrespondence

/-! # Formal integrability of the physical transport complex structure

Complexified tangent vectors use the real coordinate frame of the physical
bidisk. Their negative-imaginary eigenspace for the physical complex structure
has the vertical and horizontal transport generators as a commuting frame.
-/

noncomputable section
namespace TransportOkaGrauert.PhysicalCRIntegrability

open Complex ChartStein FrameLevi PhysicalStein
open scoped ContDiff BigOperators ComplexConjugate

abbrev Vec := Fin 4 → ℂ
abbrev Field := E → Vec

def axis : Fin 4 → E := ![(1,0),(I,0),(0,1),(0,I)]
def reVec (a : Vec) : E := ∑ i, (a i).re • axis i
def imVec (a : Vec) : E := ∑ i, (a i).im • axis i

/-- Complex-linear extension of a real covector to a complexified tangent vector. -/
def eval (a : Vec) (D : E →L[ℝ] ℂ) := ∑ i, a i * D (axis i)

/-- Coordinate formula for the complexified Lie bracket in the constant real
frame (Re z, Im z, Re μ, Im μ). -/
def bracket (A B : Field) (p : E) (i : Fin 4) :=
  eval (A p) (fderiv ℝ (fun q => B q i) p) - eval (B p) (fderiv ℝ (fun q => A q i) p)

def V : Field := fun _ => ![0,0,1,I]
def H (σ : ℂ → ℝ) : Field := fun p => ![1+p.2^2,I*(1-p.2^2),-connectionCoefficient σ p,0]

theorem eval_parts (a : Vec) (D : E →L[ℝ] ℂ) : eval a D = D (reVec a)+I*D (imVec a) := by
  simp only [eval,reVec,imVec,map_sum,map_smul,Complex.real_smul,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  calc a i * D (axis i) = ((a i).re+(a i).im*I) * D (axis i) := by rw [Complex.re_add_im]
    _ = _ := by ring

/-- The antiholomorphic eigenvector relation for `a = reVec a + i imVec a`
is equivalent to annihilation by every complex-linear physical covector. -/
theorem eigen_iff {σ : ℂ → ℝ} {p : E} (hp : ‖p.2‖ < 1) (a : Vec) :
    J σ p (reVec a) = imVec a ↔
      ∀ D : E →L[ℝ] ℂ, SatisfiesCR σ p D → eval a D = 0 := by
  constructor
  · intro g D hd
    rw [eval_parts,← g,(satisfiesCR_iff σ hp D).mp hd,← mul_assoc,I_mul_I,neg_one_mul,add_neg_cancel]
  · intro ha
    obtain ⟨h₁,h₂⟩ := rows_CR σ p
    have zero (D : E →L[ℝ] ℂ) (hd : SatisfiesCR σ p D) : D (imVec a) = I*D (reVec a) := by
      have h := ha D hd
      rw [eval_parts] at h
      linear_combination -I*h + (D (imVec a))*Complex.I_sq
    apply (coframe_bijective σ hp).1
    rw [coframe_J σ hp]
    exact Prod.ext (zero _ h₁).symm (zero _ h₂).symm

private theorem vertical_eval (p : E) (D : E →L[ℝ] ℂ) :
    eval (V p) D = D (0,1)+I*D (0,I) := by simp [eval,V,axis,Fin.sum_univ_four]

private theorem horizontal_eval (σ : ℂ → ℝ) (p : E) (D : E →L[ℝ] ℂ) :
    eval (H σ p) D = p.2^2*(D (1,0)-I*D (I,0))+(D (1,0)+I*D (I,0))-
      connectionCoefficient σ p*D (0,1) := by
  simp [eval,H,axis,Fin.sum_univ_four]
  ring

theorem generators_CR (σ : ℂ → ℝ) (p : E) (D : E →L[ℝ] ℂ) :
    SatisfiesCR σ p D ↔ eval (V p) D = 0 ∧ eval (H σ p) D = 0 := by
  rw [vertical_eval,horizontal_eval]
  constructor
  · rintro ⟨h,h'⟩
    exact ⟨by rw [h,← mul_assoc,I_mul_I,neg_one_mul,add_neg_cancel],h'⟩
  · rintro ⟨h,h'⟩
    exact ⟨by linear_combination -I*h + D (0,I)*Complex.I_sq,h'⟩

private theorem eval_combination (a b : ℂ) (v h : Vec) (D : E →L[ℝ] ℂ) :
    eval (a • v+b • h) D = a*eval v D+b*eval h D := by
  simp [eval,Finset.mul_sum,← Finset.sum_add_distrib,add_mul,mul_assoc]

private theorem horizontal_apply (p w : E) : horizontal p w = w.1-p.2^2*conj w.1 := rfl
private theorem vertical_apply (σ : ℂ → ℝ) (p w : E) :
    vertical σ p w = w.2+connectionCoefficient σ p/2*conj w.1 := rfl

/-- The two generators span exactly the minus-i eigenspace of the actual
physical complex structure in the full bidisk. -/
theorem eigenspace_frame {σ : ℂ → ℝ} {p : E} (hp : ‖p.2‖ < 1) (v : Vec) :
    J σ p (reVec v) = imVec v ↔ ∃ a b : ℂ, v = a • V p + b • H σ p := by
  rw [eigen_iff hp]
  constructor
  · intro test
    obtain ⟨r₁,r₂⟩ := rows_CR σ p
    have ea := test _ r₁
    have eb := test _ r₂
    let m := p.2^2
    let c := connectionCoefficient σ p
    have h : v 0*(1-m) + v 1*(I*(1+m)) = 0 := by
      simpa [eval,axis,horizontal_apply,Fin.sum_univ_four,m,smul_eq_mul,mul_add,mul_comm,mul_left_comm] using ea
    have k : v 0*(c/2) + v 1*((c/2)*(-I)) + v 2 + I*v 3 = 0 := by
      simpa [eval,axis,vertical_apply,Fin.sum_univ_four,c,smul_eq_mul,mul_comm,mul_left_comm] using eb
    let b := (v 0-I*v 1)/2
    have e₀ : v 0 = b*(1+m) := by dsimp [b]; linear_combination h/2
    have e₁ : I*v 1 = b*(m-1) := by dsimp [b]; linear_combination h/2
    refine ⟨-I*v 3,b,?_⟩
    funext i
    fin_cases i
    · simpa [V,H,m] using e₀
    · change v 1 = _*0 + b*(I*(1-m))
      calc v 1 = (-I)*(I*v 1) := by rw [← mul_assoc]; simp
        _ = _ := by rw [e₁]; ring
    · change v 2 = _*1+b*(-c)
      dsimp [b]; linear_combination k
    · change v 3 = (-I*v 3)*I+b*0
      rw [mul_zero,add_zero]; linear_combination (v 3)*I_sq
  · rintro ⟨a,b,rfl⟩ D hd
    rw [eval_combination,(generators_CR σ p D).mp hd |>.1,(generators_CR σ p D).mp hd |>.2]
    simp

theorem generators_independent (σ : ℂ → ℝ) (p : E) {a b : ℂ} (h : a • V p + b • H σ p = 0) :
    a = 0 ∧ b = 0 := by
  have eq (i : Fin 4) := congrFun h i
  have ea := eq 3
  have va : a = 0 := by simpa [V,H,I_ne_zero] using ea
  have h₀ := eq 0
  have h₁ := eq 1
  simp [V,H] at h₀ h₁
  refine ⟨va,?_⟩
  by_contra hb
  have e := h₀.resolve_left hb
  have f := h₁.resolve_left hb
  have : (2 : ℂ) = 0 := by linear_combination e+f
  norm_num at this

private theorem coefficient_smooth {σ : ℂ → ℝ} (hs : ContDiff ℝ ∞ σ) :
    ContDiff ℝ ∞ (connectionCoefficient σ) := by
  have ds := (hs.fderiv_right (m := ∞) (by simp)).comp (contDiff_fst (E := ℂ) (F := ℂ))
  have sx := ofRealCLM.contDiff.comp (ds.clm_apply (contDiff_const (c := (1 : ℂ))))
  have sy := ofRealCLM.contDiff.comp (ds.clm_apply (contDiff_const (c := I)))
  exact contDiff_snd.mul (((contDiff_snd.pow 2).mul (sx.sub (contDiff_const.mul sy))).sub
    (sx.add (contDiff_const.mul sy)))

theorem horizontal_smooth {σ : ℂ → ℝ} (hs : ContDiff ℝ ∞ σ) (i : Fin 4) :
    ContDiff ℝ ∞ (fun p : E => H σ p i) := by
  fin_cases i
  · exact contDiff_const.add (contDiff_snd.pow 2)
  · exact contDiff_const.mul (contDiff_const.sub (contDiff_snd.pow 2))
  · exact (coefficient_smooth hs).neg
  · exact contDiff_const

private theorem vertical_annihilates {p : E} {f : E → ℂ} (df : DifferentiableAt ℝ f p)
    (hol : DifferentiableAt ℂ (fun w => f (p.1,w)) p.2) : eval (V p) (fderiv ℝ f p) = 0 := by
  have j : HasFDerivAt (fun w : ℂ => (p.1,w)) ((0 : ℂ →L[ℝ] ℂ).prod (ContinuousLinearMap.id ℝ ℂ)) p.2 :=
    (hasFDerivAt_const p.1 p.2).prodMk (hasFDerivAt_id p.2)
  have incl := (show HasFDerivAt f (fderiv ℝ f p) (p.1,p.2) from df.hasFDerivAt).comp p.2 j
  have cmp := incl.unique (hol.hasFDerivAt.restrictScalars ℝ)
  have eq (a : ℂ) : fderiv ℝ f p (0,a) = fderiv ℂ (fun w => f (p.1,w)) p.2 a :=
    congrArg (fun L : ℂ →L[ℝ] ℂ => L a) cmp
  have mul : fderiv ℂ (fun w => f (p.1,w)) p.2 I = I*fderiv ℂ (fun w => f (p.1,w)) p.2 1 := by
    simpa only [smul_eq_mul,mul_one] using (fderiv ℂ (fun w => f (p.1,w)) p.2).map_smul I (1:ℂ)
  rw [vertical_eval,eq,eq,mul,← mul_assoc,I_mul_I,neg_one_mul,add_neg_cancel]

/-- The coordinate Lie bracket of the two antiholomorphic generators is zero.
The horizontal coefficients are holomorphic polynomials in velocity. -/
theorem bracket_vh {σ : ℂ → ℝ} (hs : ContDiff ℝ ∞ σ) :
    bracket V (H σ) = 0 := by
  funext p i
  have fibre : DifferentiableAt ℂ (fun w => H σ (p.1,w) i) p.2 := by
    fin_cases i <;> dsimp [H,connectionCoefficient] <;> fun_prop
  unfold bracket
  rw [vertical_annihilates ((horizontal_smooth hs i).differentiable (by simp) p) fibre]
  have eq : (fun q : E => V q i) = fun _ => V p i := rfl
  simp [eq,eval]

end TransportOkaGrauert.PhysicalCRIntegrability
