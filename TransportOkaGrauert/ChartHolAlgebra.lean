import TransportOkaGrauert.ChartStein

namespace TransportOkaGrauert.ChartStein
noncomputable section
open Complex
open scoped ContDiff

theorem cr_add {σ p} {A B : E →L[ℝ] ℂ} (ha : SatisfiesCR σ p A) (hb : SatisfiesCR σ p B) :
    SatisfiesCR σ p (A+B) := by
  constructor
  · simp only [ContinuousLinearMap.add_apply,ha.1,hb.1]; ring
  · simp only [ContinuousLinearMap.add_apply]; linear_combination ha.2 + hb.2

theorem holAt_const (σ : ℂ → ℝ) (p : E) (c : ℂ) : HolAt σ (fun _ => c) p := by
  refine ⟨contDiffAt_const, ?_⟩
  simp [SatisfiesCR]

theorem HolAt.add {σ p f g} (hf : HolAt σ f p) (hg : HolAt σ g p) :
    HolAt σ (fun q => f q + g q) p := by
  have h := (hf.1.differentiableAt (by simp)).hasFDerivAt.add
    (hg.1.differentiableAt (by simp)).hasFDerivAt
  exact ⟨hf.1.add hg.1,h.fderiv ▸ cr_add hf.2 hg.2⟩

theorem HolAt.mul {σ p f g} (hf : HolAt σ f p) (hg : HolAt σ g p) :
    HolAt σ (fun q => f q * g q) p := by
  have h := (hf.1.differentiableAt (by simp)).hasFDerivAt.mul
    (hg.1.differentiableAt (by simp)).hasFDerivAt
  exact ⟨hf.1.mul hg.1,h.fderiv ▸ cr_add (cr_smul hg.2 _) (cr_smul hf.2 _)⟩

theorem HolAt.sub {σ p f g} (hf : HolAt σ f p) (hg : HolAt σ g p) :
    HolAt σ (fun q => f q - g q) p := by
  have h := hf.add ((holAt_const σ p (-1)).mul hg)
  simpa only [neg_one_mul, sub_eq_add_neg] using h
/-- The chart Stein properties only use the germ of the conformal factor on the
physical base. In particular its exterior cutoff does not change the result. -/
theorem stein_congr {σ τ : ℂ → ℝ} {U : Set ℂ} (openU : IsOpen U)
    (eq : Set.EqOn σ τ U) (h : HasSteinProperties σ U) : HasSteinProperties τ U := by
  have hol (f : E → ℂ) : HolOn σ U f ↔ HolOn τ U f := by
    unfold HolOn
    apply forall_congr'
    intro p
    have germ : σ =ᶠ[nhds p.val.1.val] τ := Filter.mem_of_superset
      (openU.mem_nhds p.property.1) (fun _ hx => eq hx)
    simp only [HolAt, SatisfiesCR, connectionCoefficient, point, germ.fderiv_eq]
  have teq : tests σ U = tests τ U := by
    ext g
    simp only [tests, Set.mem_setOf_eq, hol]
  refine ⟨fun K hK => teq ▸ h.convex K hK, ?_, ?_⟩
  · intro x y hne
    obtain ⟨f,hf,sep⟩ := h.separates x y hne
    exact ⟨f,(hol f).mp hf,sep⟩
  · intro x
    obtain ⟨f,g,hf,hg,bij⟩ := h.coordinates x
    exact ⟨f,g,(hol f).mp hf,(hol g).mp hg,bij⟩

end
end TransportOkaGrauert.ChartStein
