import TransportOkaGrauert.PhysicalSteinArea

/-! # Exponential changes of potential for the physical complex Hessian -/

noncomputable section
namespace TransportOkaGrauert.PhysicalLeviCalculus

open ChartStein PhysicalStein FrameLevi Filter
open scoped ContDiff Topology

def potential (a b : ℝ) (f g : E → ℝ) (p : E) := a * f p + Real.exp (b * g p)

theorem potential_smooth (a b : ℝ) {f g : E → ℝ} {p : E} {n : WithTop ℕ∞}
    (hf : ContDiffAt ℝ n f p) (hg : ContDiffAt ℝ n g p) : ContDiffAt ℝ n (potential a b f g) p :=
  (contDiffAt_const.mul hf).add ((contDiffAt_const.mul hg).exp)

theorem gradient (a b : ℝ) {f g : E → ℝ} {p : E} (hf : DifferentiableAt ℝ f p)
    (hg : DifferentiableAt ℝ g p) (v : E) :
    fderiv ℝ (potential a b f g) p v = a*fderiv ℝ f p v +
      (b*Real.exp (b*g p))*fderiv ℝ g p v := by
  have d := (hf.hasFDerivAt.const_mul a).add ((hg.hasFDerivAt.const_mul b).exp)
  change HasFDerivAt (potential a b f g) _ p at d
  rw [d.fderiv]
  simp
  ring

private def component (j : E → E →L[ℝ] E) (f : E → ℝ) (w y : E) := -fderiv ℝ f y (j y w)

private theorem component_diff {j : E → E →L[ℝ] E} {f : E → ℝ} {p : E}
    (dj : DifferentiableAt ℝ j p) (df : ContDiffAt ℝ 2 f p) (w : E) :
    DifferentiableAt ℝ (component j f w) p :=
  (((df.fderiv_right (m := 1) (by decide)).differentiableAt one_ne_zero).clm_apply
    (dj.clm_apply (differentiableAt_const w))).neg

private theorem exterior {j : E → E →L[ℝ] E} {f : E → ℝ} {p : E}
    (dj : DifferentiableAt ℝ j p) (df : ContDiffAt ℝ 2 f p) (v w : E) :
    ddC j f p v w = fderiv ℝ (component j f w) p v - fderiv ℝ (component j f v) p w := by
  have hd := (df.fderiv_right (m := 1) (by decide)).differentiableAt one_ne_zero
  have dform : DifferentiableAt ℝ (dc j f) p :=
    (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℝ) (0 : Fin 1)).differentiableAt.comp
      p (hd.clm_comp dj).neg
  have r0 : (0 : Fin 2).removeNth ![v,w] = ![w] := by funext i; fin_cases i; rfl
  have r1 : (1 : Fin 2).removeNth ![v,w] = ![v] := by funext i; fin_cases i; rfl
  rw [ddC,extDeriv_apply dform]
  simp only [Nat.reduceAdd,Fin.sum_univ_two,r0,r1,Fin.val_zero,Fin.val_one,pow_zero,pow_one,
    one_smul,neg_one_smul,Matrix.cons_val_zero,Matrix.cons_val_one,sub_eq_add_neg]
  rfl

theorem levi_potential (a b : ℝ) {j : E → E →L[ℝ] E} {f g : E → ℝ} {p : E}
    (dj : DifferentiableAt ℝ j p) (df : ContDiffAt ℝ 2 f p) (dg : ContDiffAt ℝ 2 g p)
    (v : E) (jj : j p (j p v) = -v) :
    let c := b*Real.exp (b*g p)
    ddC j (potential a b f g) p v (j p v) = a*ddC j f p v (j p v) + c*ddC j g p v (j p v) +
      b*c*((fderiv ℝ g p v)^2 + (fderiv ℝ g p (j p v))^2) := by
  let c := fun y => b*Real.exp (b*g y)
  have dc := ((((dg.differentiableAt (by decide)).hasFDerivAt.const_mul b).exp).const_mul b)
  have d (w u : E) : fderiv ℝ (component j (potential a b f g) w) p u =
      a*fderiv ℝ (component j f w) p u + c p*fderiv ℝ (component j g w) p u +
        b*c p*fderiv ℝ g p u*component j g w p := by
    have d₁ := (component_diff dj df w).hasFDerivAt.const_mul a
    have d₂ := dc.mul (component_diff dj dg w).hasFDerivAt
    have h := (d₁.add d₂).congr_of_eventuallyEq (f₁ := component j (potential a b f g) w) (by
      filter_upwards [df.eventually (by decide),dg.eventually (by decide)] with y fy gy
      simp only [Pi.add_apply,Pi.mul_apply,component,gradient a b (fy.differentiableAt (by decide)) (gy.differentiableAt (by decide))]
      ring)
    rw [h.fderiv]
    simp [c]
    ring
  rw [exterior dj (potential_smooth a b df dg),exterior dj df,exterior dj dg,d,d]
  simp [c,component,jj]
  ring

theorem levi_linear (L : E →L[ℝ] ℝ) {σ : ℂ → ℝ} (hs : ContDiff ℝ ∞ σ) {p : E}
    (hp : ‖p.2‖ < 1) (v : E) :
    ddC (J σ) L p v (J σ p v) = L (fderiv ℝ (J σ) p (J σ p v) v) -
      L (fderiv ℝ (J σ) p v (J σ p v)) := by
  have dJ := (J_smooth hs hp).differentiableAt (by simp)
  have eq (w u : E) : fderiv ℝ (component (J σ) L w) p u = -L (fderiv ℝ (J σ) p u w) := by
    have d := (L.hasFDerivAt.comp p (dJ.hasFDerivAt.clm_apply (hasFDerivAt_const w p))).neg
    have funEq : component (J σ) L w = fun q => -(L (J σ q w)) := by funext q; simp [component]
    change HasFDerivAt (fun q => -(L (J σ q w))) _ p at d
    rw [funEq,d.fderiv]
    simp
  rw [exterior dJ L.contDiff.contDiffAt,eq,eq]
  ring

end TransportOkaGrauert.PhysicalLeviCalculus
