import TransportOkaGrauert.ScalarGeneralGauss

/-! # Quadratic radial vanishing of the exponential-map Jacobian -/

noncomputable section
namespace TransportOkaGrauert.ScalarGeneralKernel
open Complex Metric Set Filter SimpleRadialVariation ConformalFrame SimpleDiskTarget
open scoped ContDiff Topology Manifold

/-- Oriented area Jacobian of the exponential between initial isometric
velocity coordinates and Riemannian base area. -/
def alpha (σ : ℂ → ℝ) (E : ℂ × ℂ → ℂ) (q : ℂ × ℂ) :=
  Real.exp (2*σ (E q)) * (verticalDerivative E q).det

theorem alpha_smooth {σ : ℂ → ℝ} {E : ℂ × ℂ → ℂ} (hs : ContDiff ℝ ∞ σ) (sE : ContDiff ℝ ∞ E) :
    ContDiff ℝ ∞ (alpha σ E) := by
  have s : ContDiff ℝ ∞ (verticalDerivative E) := (sE.fderiv_right (m := ∞) (by simp)).clm_comp contDiff_const
  have m (v : ℂ) := s.clm_apply (contDiff_const (c := v))
  unfold alpha
  simp_rw [determinant_formula]
  exact ((contDiff_const.mul (hs.comp sE)).exp).mul
    (((reCLM.contDiff.comp (m 1)).mul (imCLM.contDiff.comp (m I))).sub
      ((reCLM.contDiff.comp (m I)).mul (imCLM.contDiff.comp (m 1))))

private theorem determinant_defect (M : ℂ →L[ℝ] ℂ) (c : ℝ) :
    (c*M.det)^2 = (1+defect M c 1 1)*(1+defect M c I I) - (defect M c 1 I)^2 := by
  simp [determinant_formula,defect,dot]; ring

private def cart (q : (ℂ × ℝ) × ℝ) : ℂ × ℂ := (q.1.1,(q.1.2:ℂ)+(q.2:ℂ)*I)
private def split (q : ℂ × ℂ) : (ℂ × ℝ) × ℝ := ((q.1,q.2.re),q.2.im)

private theorem cart_smooth : ContDiff ℝ ∞ cart :=
  (contDiff_fst.comp contDiff_fst).prodMk ((ofRealCLM.contDiff.comp (contDiff_snd.comp contDiff_fst)).add
    ((ofRealCLM.contDiff.comp contDiff_snd).mul contDiff_const))
private theorem split_smooth : ContDiff ℝ ∞ split :=
  (contDiff_fst.prodMk (reCLM.contDiff.comp contDiff_snd)).prodMk (imCLM.contDiff.comp contDiff_snd)

private theorem cutoff_pair {U Q : Set (ℂ × ℂ)} (op : IsOpen U) (closed : IsClosed Q) (inside : Q ⊆ U) :
    ∃ χ : ℂ × ℂ → ℝ, ContDiff ℝ ∞ χ ∧ (∀ p ∈ Q, χ =ᶠ[𝓝 p] fun _ => 1) ∧
      ∀ p ∉ U, χ =ᶠ[𝓝 p] fun _ => 0 := by
  obtain ⟨χ,zero,one,_⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed (𝓘(ℝ,ℂ × ℂ)) (n := ⊤)
    op.isClosed_compl closed (Set.disjoint_left.mpr (fun _ hU hQ => hU (inside hQ)))
  exact ⟨χ,contMDiff_iff_contDiff.mp χ.contMDiff,mem_nhdsSet_iff_forall.mp one,mem_nhdsSet_iff_forall.mp zero⟩

private theorem defect_smooth {E : ℂ × ℂ → ℂ} {σ : ℂ → ℝ} (sE : ContDiff ℝ ∞ E) (sσ : ContDiff ℝ ∞ σ) (u v : ℂ) :
    ContDiff ℝ ∞ (fun q => defect (verticalDerivative E q) (Real.exp (2*σ (E q))) u v) := by
  have M : ContDiff ℝ ∞ (verticalDerivative E) := (sE.fderiv_right (m := ∞) (by simp)).clm_comp contDiff_const
  have m (x : ℂ) := M.clm_apply (contDiff_const (c := x))
  exact (((contDiff_const.mul (sσ.comp sE)).exp).mul
    (((reCLM.contDiff.comp (m u)).mul (reCLM.contDiff.comp (m v))).add
      ((imCLM.contDiff.comp (m u)).mul (imCLM.contDiff.comp (m v))))).sub contDiff_const

/-- Smooth divisibility of the squared Jacobian defect by squared velocity.
The centre is a free complex parameter throughout. -/
theorem squared_jacobian_factor {σ : ℂ → ℝ} (simple : SimpleMetric σ) {E : ℂ × ℂ → ℂ} (sE : ContDiff ℝ ∞ E)
    (family : ∀ a ∈ ball (0:ℂ) 1, ∃ C : Coordinates σ a, C.endpoint = fun v => E (a,v))
    {U Q : Set (ℂ × ℂ)} (op : IsOpen U) (closed : IsClosed Q) (inside : Q ⊆ U)
    (retained : ∀ q ∈ U, q.1 ∈ ball (0:ℂ) 1 ∧ ∀ t ∈ Icc (0:ℝ) 1, ‖E (q.1,t • q.2)‖ ≤ 1) :
    ∃ k : ℂ × ℂ → ℝ, ContDiff ℝ ∞ k ∧ ∀ q ∈ Q,
      (fun p => (alpha σ E p)^2) =ᶠ[𝓝 q] (fun p => 1 + Complex.normSq p.2*k p) := by
  obtain ⟨χ,sχ,one,zero⟩ := cutoff_pair op closed inside
  let D (u v : ℂ) (q : ℂ × ℂ) := defect (verticalDerivative E q) (Real.exp (2*σ (E q))) u v
  let H (u v : ℂ) (q : (ℂ × ℝ) × ℝ) := χ (cart q) * D u v (cart q)
  have hH (u v : ℂ) : ContDiff ℝ ∞ (H u v) := (sχ.comp cart_smooth).mul ((defect_smooth sE simple.smooth u v).comp cart_smooth)
  have rows (a : ℂ) (s t : ℝ) :
      H 1 1 ((a,s),t)*s + H 1 I ((a,s),t)*t = 0 ∧ H 1 I ((a,s),t)*s + H I I ((a,s),t)*t = 0 := by
    let q := cart ((a,s),t)
    by_cases hq : q ∈ U
    · obtain ⟨ha,seg⟩ := retained q hq
      obtain ⟨C,ce⟩ := family a ha
      have ret : q.2 ∈ SimpleRadialStar.retained C.endpoint 1 := by
        intro u hu
        simpa [ce] using seg u hu
      have raw := defect_radial C simple ret
      have dM := verticalDerivative_eq (sE.differentiable (by simp) q)
      change verticalDerivative E q = fderiv ℝ (fun w => E (a,w)) q.2 at dM
      rw [← ce] at dM
      change defect (fderiv ℝ C.endpoint q.2) _ 1 1 * _ + _ = 0 ∧ _ at raw
      rw [← dM,ce] at raw
      have rr : q.2.re = s := by simp [q,cart]
      have ri : q.2.im = t := by simp [q,cart]
      rw [rr,ri] at raw
      change χ q*D 1 1 q*s + χ q*D 1 I q*t = 0 ∧ χ q*D 1 I q*s + χ q*D I I q*t = 0
      change D 1 1 q*s+D 1 I q*t = 0 ∧ D 1 I q*s+D I I q*t = 0 at raw
      constructor
      · linear_combination χ q*raw.1
      · linear_combination χ q*raw.2
    · have e : χ q = 0 := (zero q hq).self_of_nhds
      change χ q*_ *s+χ q*_ *t = 0 ∧ χ q*_ *s+χ q*_ *t = 0
      simp [e]
  obtain ⟨k,sk,value⟩ := SmoothRadialHessian.radialKernelFactor (hH 1 1) (hH 1 I) (hH I I)
    (fun a s t => (rows a s t).1) (fun a s t => (rows a s t).2)
  refine ⟨k ∘ split,sk.comp split_smooth,fun q hq => ?_⟩
  filter_upwards [one q hq] with p hp
  obtain ⟨h1,h2,h3⟩ := value p.1 p.2.re p.2.im
  have eq : cart ((p.1,p.2.re),p.2.im) = p := by simp [cart]
  change χ p = 1 at hp
  simp only [H,eq,hp,one_mul] at h1 h2 h3
  change (Real.exp (2*σ (E p))*(verticalDerivative E p).det)^2 = _
  rw [determinant_defect]
  change (1+D 1 1 p)*(1+D I I p)-(D 1 I p)^2 = _
  rw [h1,h2,h3]
  simp [Complex.normSq_apply,split]; ring

end TransportOkaGrauert.ScalarGeneralKernel
