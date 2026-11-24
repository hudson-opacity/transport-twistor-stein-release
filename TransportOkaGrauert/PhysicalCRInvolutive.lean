import TransportOkaGrauert.PhysicalCRIntegrability

/-! # Involutivity of all local antiholomorphic vector fields

The bracket of any two differentiable sections of the physical antiholomorphic
tangent bundle is again a section, on every open subset of the physical bidisk.
-/

noncomputable section
namespace TransportOkaGrauert.PhysicalCRIntegrability
open Complex Set Filter PhysicalStein FrameLevi ChartStein
open scoped ContDiff Topology

private def sectionOf (σ : ℂ → ℝ) (a b : E → ℂ) : Field := fun p => a p • V p+b p • H σ p
private def act (A : Field) (f : E → ℂ) (p : E) := eval (A p) (fderiv ℝ f p)

private theorem eval_lin (a b : ℂ) (v h : Vec) (D : E →L[ℝ] ℂ) :
    eval (a • v+b • h) D = a*eval v D+b*eval h D := by
  simp [eval,Finset.mul_sum,← Finset.sum_add_distrib,add_mul,mul_assoc]

private theorem product_rule (v : Vec) {f g : E → ℂ} {p : E}
    (hf : DifferentiableAt ℝ f p) (hg : DifferentiableAt ℝ g p) :
    eval v (fderiv ℝ (fun q => f q*g q) p) =
      eval v (fderiv ℝ f p)*g p + f p*eval v (fderiv ℝ g p) := by
  change eval v (fderiv ℝ (f*g) p) = _
  rw [(hf.hasFDerivAt.mul hg.hasFDerivAt).fderiv]
  simp [eval,Fin.sum_univ_four,smul_eq_mul]
  ring

private theorem sum_rule (v : Vec) {f g : E → ℂ} {p : E}
    (hf : DifferentiableAt ℝ f p) (hg : DifferentiableAt ℝ g p) :
    eval v (fderiv ℝ (fun q => f q+g q) p) = eval v (fderiv ℝ f p) + eval v (fderiv ℝ g p) := by
  change eval v (fderiv ℝ (f+g) p) = _
  rw [(hf.hasFDerivAt.add hg.hasFDerivAt).fderiv]
  simp [eval,mul_add,Finset.sum_add_distrib]

private theorem row_rule {σ : ℂ → ℝ} (hs : ContDiff ℝ ∞ σ)
    {a b : E → ℂ} {p : E} (ha : DifferentiableAt ℝ a p) (hb : DifferentiableAt ℝ b p)
    (ξ : Vec) (i : Fin 4) :
    eval ξ (fderiv ℝ (fun q => sectionOf σ a b q i) p) =
      eval ξ (fderiv ℝ a p)*V p i + eval ξ (fderiv ℝ b p)*H σ p i +
      b p*eval ξ (fderiv ℝ (fun q => H σ q i) p) := by
  have dV : DifferentiableAt ℝ (fun q : E => V q i) p := differentiableAt_const _
  have dH := (horizontal_smooth hs i).differentiable (by simp) p
  change eval ξ (fderiv ℝ (fun q => a q*V q i+b q*H σ q i) p) = _
  have haV : DifferentiableAt ℝ (fun q => a q*V q i) p := ha.mul dV
  have hbH : DifferentiableAt ℝ (fun q => b q*H σ q i) p := hb.mul dH
  rw [sum_rule ξ haV hbH,product_rule ξ ha dV, product_rule ξ hb dH]
  have h : (fun q : E => V q i) = fun _ => V p i := rfl
  simp [h,eval,add_assoc]

private theorem bracket_sections {σ : ℂ → ℝ} (hs : ContDiff ℝ ∞ σ) {a b c d : E → ℂ} {p : E}
    (ha : DifferentiableAt ℝ a p) (hb : DifferentiableAt ℝ b p)
    (hc : DifferentiableAt ℝ c p) (hd : DifferentiableAt ℝ d p) :
    bracket (sectionOf σ a b) (sectionOf σ c d) p =
      (act (sectionOf σ a b) c p-act (sectionOf σ c d) a p) • V p +
      (act (sectionOf σ a b) d p-act (sectionOf σ c d) b p) • H σ p := by
  funext i
  have h : (fun q : E => V q i) = fun _ => V p i := rfl
  have bracket₀ := congrFun (congrFun (bracket_vh hs) p) i
  have kill : eval (V p) (fderiv ℝ (fun q => H σ q i) p) = 0 := by
    simpa [bracket,h,eval] using bracket₀
  unfold bracket
  rw [row_rule hs hc hd,row_rule hs ha hb]
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,act,sectionOf,eval_lin,kill]
  ring

private def wV (A : Field) (p : E) := -I*A p 3
private def wH (A : Field) (p : E) := (A p 0-I*A p 1)/2

private theorem represent {σ : ℂ → ℝ} {p : E} (hp : ‖p.2‖ < 1) (A : Field)
    (h : J σ p (reVec (A p)) = imVec (A p)) : A p = sectionOf σ (wV A) (wH A) p := by
  obtain ⟨a,b,hab⟩ := (eigenspace_frame hp _).mp h
  have v : wV A p = a := by simp [wV,hab,V,H,mul_comm,mul_left_comm]
  have w : wH A p = b := by
    simp [wH,hab,V,H]; linear_combination -(b*(1-p.2^2)/2)*I_sq
  simpa [sectionOf,v,w] using hab

/-- Formal integrability in the bracket formulation, for arbitrary differentiable
local sections on an open set in physical coordinates. -/
theorem involutive {σ : ℂ → ℝ} (hs : ContDiff ℝ ∞ σ) {U : Set E} (hU : IsOpen U)
    (inside : ∀ p ∈ U, ‖p.2‖ < 1) (A B : Field)
    (dA : ∀ p ∈ U, ∀ i, DifferentiableAt ℝ (fun q => A q i) p)
    (dB : ∀ p ∈ U, ∀ i, DifferentiableAt ℝ (fun q => B q i) p)
    (hA : ∀ p ∈ U, J σ p (reVec (A p)) = imVec (A p))
    (hB : ∀ p ∈ U, J σ p (reVec (B p)) = imVec (B p)) (p : E) (hp : p ∈ U) :
    J σ p (reVec (bracket A B p)) = imVec (bracket A B p) := by
  have localA : A =ᶠ[𝓝 p] sectionOf σ (wV A) (wH A) := by
    filter_upwards [hU.mem_nhds hp] with q hq using represent (inside q hq) A (hA q hq)
  have localB : B =ᶠ[𝓝 p] sectionOf σ (wV B) (wH B) := by
    filter_upwards [hU.mem_nhds hp] with q hq using represent (inside q hq) B (hB q hq)
  have eq : bracket A B p = bracket (sectionOf σ (wV A) (wH A)) (sectionOf σ (wV B) (wH B)) p := by
    funext i
    have ea' : (fun q => A q i) =ᶠ[𝓝 p] fun q => sectionOf σ (wV A) (wH A) q i := localA.mono fun q hq => congrFun hq i
    have eb' : (fun q => B q i) =ᶠ[𝓝 p] fun q => sectionOf σ (wV B) (wH B) q i := localB.mono fun q hq => congrFun hq i
    have ea := ea'.fderiv_eq (𝕜 := ℝ)
    have eb := eb'.fderiv_eq (𝕜 := ℝ)
    simp only [bracket,localA.self_of_nhds,localB.self_of_nhds,ea,eb]
  apply (eigenspace_frame (inside p hp) _).mpr
  have dH (Y : Field) (dY : ∀ i, DifferentiableAt ℝ (fun q => Y q i) p) : DifferentiableAt ℝ (wH Y) p := by
    unfold wH
    have sub : DifferentiableAt ℝ (fun q => Y q 0-I*Y q 1) p := (dY 0).sub ((differentiableAt_const (I:ℂ)).mul (dY 1))
    simp only [div_eq_mul_inv]
    exact sub.mul (differentiableAt_const _)
  rw [eq,bracket_sections hs (a := wV A) (b := wH A) (c := wV B) (d := wH B)
    ((differentiableAt_const (-I)).mul (dA p hp 3)) (dH A (dA p hp))
    ((differentiableAt_const (-I)).mul (dB p hp 3)) (dH B (dB p hp))]
  exact ⟨_,_,rfl⟩

end TransportOkaGrauert.PhysicalCRIntegrability
