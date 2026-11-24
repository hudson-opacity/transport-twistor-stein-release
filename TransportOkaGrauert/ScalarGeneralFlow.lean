import TransportOkaGrauert.ScalarGeneralCauchy

/-! Smooth unrestricted transport integration on a compact escaping region.
A detector outside the region furnishes a smooth clock along the flow. Its
construction does not differentiate exit times. -/
noncomputable section
namespace TransportOkaGrauert.ScalarGeneralFlow
open Set Metric MeasureTheory Filter ScalarGeneralCauchy
open scoped ContDiff Topology Interval

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

/-- An additive, jointly smooth real-time flow, with state first. -/
structure SmoothFlow (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  val : E × ℝ → E
  smooth : ContDiff ℝ ∞ val
  initial : ∀ p, val (p,0) = p
  advance : ∀ p t s, val (val (p,t), s) = val (p,t+s)

variable (Φ : SmoothFlow E)
variable {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/-- Signed integral over a backward flow segment of variable duration. -/
def history (f : E → G) (p : E × ℝ) : G := ∫ t in (0:ℝ)..p.2, f (Φ.val (p.1,-t))

theorem history_smooth {f : E → G} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (history Φ f) := by
  let g (v : (E × ℝ) × ℝ) := f (Φ.val (v.1.1,-(v.1.2*v.2)))
  have hg : ContDiff ℝ ∞ g := hf.comp (Φ.smooth.comp ((contDiff_fst.comp contDiff_fst).prodMk
    (((contDiff_snd.comp contDiff_fst).mul contDiff_snd).neg)))
  have h := contDiff_snd.smul (integral_smooth hg one_pos)
  convert h using 1
  funext p
  simpa [history,g] using (intervalIntegral.smul_integral_comp_mul_left (a := 0) (b := 1)
    (fun t => f (Φ.val (p.1,-t))) p.2).symm

omit [ProperSpace E] [NormedSpace ℝ G] [CompleteSpace G] in
private theorem along_cont {f : E → G} (hf : Continuous f) (p : E) : Continuous (fun t : ℝ => f (Φ.val (p,-t))) :=
  hf.comp (Φ.smooth.continuous.comp (continuous_const.prodMk continuous_id.neg))

omit [ProperSpace E] in
theorem history_derivative {f : E → G} (hf : Continuous f) (p : E) (s : ℝ) :
    HasDerivAt (fun t => history Φ f (p,t)) (f (Φ.val (p,-s))) s := by
  have hc := along_cont Φ hf p
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _) hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

omit [ProperSpace E] [CompleteSpace G] in
theorem history_advance {f : E → G} (hf : Continuous f) (p : E) (h s : ℝ) :
    history Φ f (Φ.val (p,h),s) = history Φ f (p,s-h) - history Φ f (p,-h) := by
  let g (t : ℝ) := f (Φ.val (p,-t))
  have hc : Continuous g := along_cont Φ hf p
  have trans (t : ℝ) : f (Φ.val (Φ.val (p,h), -t)) = g (t + -h) := by
    rw [Φ.advance]
    simp [g]
  unfold history
  simp only [trans]
  rw [intervalIntegral.integral_comp_add_right, intervalIntegral.integral_interval_sub_left
    (hc.intervalIntegrable 0 (s-h)) (hc.intervalIntegrable 0 (-h))]
  simp [g,sub_eq_add_neg]

/-- Compactness turns individual backward visits to the exterior detector into
a uniform time and a strictly positive lower bound for accumulated detection. -/
theorem uniform_detection {β : E → ℝ} (hβ : ContDiff ℝ ∞ β) (hn : ∀ p, 0 ≤ β p)
    {K : Set E} (hK : IsCompact K) (escape : ∀ p ∈ K, ∃ t : ℝ, 0 < t ∧ 0 < β (Φ.val (p,-t))) :
    ∃ T δ : ℝ, 0 < T ∧ 0 < δ ∧ ∀ p ∈ K, δ ≤ history Φ β (p,T) := by
  classical
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1,1,one_pos,one_pos,by simp⟩
  let U (n : ℕ) := {p : E | 0 < history Φ β (p, (n:ℝ)+1)}
  have ho (n : ℕ) : IsOpen (U n) := isOpen_lt continuous_const
    ((history_smooth Φ hβ).continuous.comp (continuous_id.prodMk continuous_const))
  have covered : K ⊆ ⋃ n, U n := by
    intro p hp
    obtain ⟨t,ht,hval⟩ := escape p hp
    obtain ⟨n,hn'⟩ := exists_nat_gt t
    apply mem_iUnion.mpr; refine ⟨n, ?_⟩
    exact intervalIntegral.integral_pos (by positivity : 0 < (n:ℝ)+1)
      (along_cont Φ hβ.continuous p).continuousOn (fun _ _ => hn _)
      ⟨t, ⟨ht.le, by linarith⟩, hval⟩
  have mono : Monotone U := by
    intro i j hij p hp
    change 0 < history Φ β (p,(j:ℝ)+1)
    change 0 < history Φ β (p,(i:ℝ)+1) at hp
    apply lt_of_lt_of_le hp
    have hij' : (i:ℝ) ≤ (j:ℝ) := by exact_mod_cast hij
    exact intervalIntegral.integral_mono_interval le_rfl (by positivity) (by linarith)
      (Eventually.of_forall fun _ => hn _) ((along_cont Φ hβ.continuous p).intervalIntegrable _ _)
  obtain ⟨n,H⟩ := hK.elim_directed_cover U ho covered mono.directed_le
  obtain ⟨p,hp,hm⟩ := hK.exists_isMinOn hne
    (((history_smooth Φ hβ).continuous.comp (continuous_id.prodMk (continuous_const (y := (n:ℝ)+1)))).continuousOn)
  exact ⟨(n:ℝ)+1, history Φ β (p,(n:ℝ)+1), by positivity, H hp, fun x hx => isMinOn_iff.mp hm x hx⟩


/-- A regularized elapsed time constructed from the accumulated exterior detector. -/
def clock (β : E → ℝ) (χ : ℝ → ℝ) (T : ℝ) (p : E) := ∫ s in (0:ℝ)..T, χ (history Φ β (p,s))

private theorem clock_rate {β : E → ℝ} (hβ : ContDiff ℝ ∞ β) {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    {T : ℝ} (hT : 0 < T) (p : E) (hin : β p = 0) :
    HasDerivAt (fun h => clock Φ β χ T (Φ.val (p,h))) (χ 0 - χ (history Φ β (p,T))) 0 := by
  let g (v : ℝ × ℝ) := χ (history Φ β (Φ.val (p,v.1),v.2))
  have hg : ContDiff ℝ ∞ g := hχ.comp ((history_smooth Φ hβ).comp
    ((Φ.smooth.comp (contDiff_const.prodMk contDiff_fst)).prodMk contDiff_snd))
  let b (s : ℝ) := χ (history Φ β (p,s))
  have hb : ContDiff ℝ ∞ b := hχ.comp ((history_smooth Φ hβ).comp (contDiff_const.prodMk contDiff_id))
  have hd (s : ℝ) : deriv (fun h => g (h,s)) 0 = -deriv b s := by
    have d (a : ℝ) : HasDerivAt (fun h : ℝ => history Φ β (p, a-h)) (-β (Φ.val (p,-a))) 0 := by
      have h := (history_derivative Φ hβ.continuous p (a-(0:ℝ))).comp (0:ℝ)
        ((hasDerivAt_const (0:ℝ) a).sub (hasDerivAt_id (0:ℝ)))
      simpa using h
    have da := (d s).sub (d 0)
    simp only [zero_sub, neg_zero, Φ.initial, hin, sub_zero] at da
    have he : HasDerivAt (fun h => history Φ β (Φ.val (p,h),s)) (-β (Φ.val (p,-s))) 0 := by
      simpa only [history_advance Φ hβ.continuous] using da
    have hleft := ((hχ.differentiable (by simp) _).hasDerivAt.comp 0 he).deriv
    have hright := ((hχ.differentiable (by simp) _).hasDerivAt.comp s (history_derivative Φ hβ.continuous p s)).deriv
    change deriv (χ ∘ fun h => history Φ β (Φ.val (p,h),s)) 0 = -deriv (χ ∘ fun t => history Φ β (p,t)) s
    rw [hleft,hright,Φ.initial,mul_neg]
  have hs := integral_smooth hg hT
  apply (hs.differentiable (by simp) 0).hasDerivAt.congr_deriv
  rw [← fderiv_apply_one_eq_deriv, integral_direction hg 0 1 hT]
  simp_rw [fderiv_apply_one_eq_deriv, hd]
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_deriv_eq_sub (fun s _ => hb.differentiable (by simp) s)
    ((hb.continuous_deriv (by simp)).intervalIntegrable _ _)]
  simp [b,history]

/-- Every uniformly escaping compact set admits a global smooth clock advancing
at unit rate there. Its construction respects every symmetry of the detector
and of the flow, including translations on an angular cover. -/
theorem exists_clock {β : E → ℝ} (hβ : ContDiff ℝ ∞ β) (hn : ∀ p, 0 ≤ β p)
    {K : Set E} (hK : IsCompact K) (hin : ∀ p ∈ K, β p = 0)
    (escape : ∀ p ∈ K, ∃ t : ℝ, 0 < t ∧ 0 < β (Φ.val (p,-t))) :
    ∃ τ : E → ℝ, ContDiff ℝ ∞ τ ∧ (∀ p ∈ K, HasDerivAt (fun s => τ (Φ.val (p,s))) 1 0) ∧
      ∀ A : E → E, (∀ p t, Φ.val (A p,t) = A (Φ.val (p,t))) → (∀ p, β (A p) = β p) → ∀ p, τ (A p) = τ p := by
  obtain ⟨T,δ,hT,hδ,H⟩ := uniform_detection Φ hβ hn hK escape
  let χ : ContDiffBump (0:ℝ) := ⟨δ/2, δ, by positivity, by linarith⟩
  have hs : ContDiff ℝ ∞ (clock Φ β χ T) := integral_smooth (χ.contDiff.comp (history_smooth Φ hβ)) hT
  refine ⟨clock Φ β χ T, hs, ?_, ?_⟩
  · intro p hp
    have hi : χ 0 = 1 := χ.one_of_mem_closedBall (mem_closedBall_self (by change 0 ≤ δ/2; positivity))
    have ho : χ (history Φ β (p,T)) = 0 := χ.zero_of_le_dist (by
      rw [Real.dist_0_eq_abs, abs_of_pos (hδ.trans_le (H p hp))]; exact H p hp)
    simpa only [hi,ho,sub_zero] using clock_rate Φ hβ χ.contDiff hT p (hin p hp)
  · intro A hA hβA p
    simp only [clock,history,hA,hβA]

/-- Integrating any smooth source for one clock duration supplies a global
smooth primitive on the region where the clock advances at unit rate. -/
theorem integrate_clock {τ : E → ℝ} (hτ : ContDiff ℝ ∞ τ) (f : E → G) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun p => history Φ f (p,τ p)) ∧
    ∀ p, HasDerivAt (fun s => τ (Φ.val (p,s))) 1 0 →
      HasDerivAt (fun s => history Φ f (Φ.val (p,s),τ (Φ.val (p,s)))) (f p) 0 := by
  refine ⟨(history_smooth Φ hf).comp (contDiff_id.prodMk hτ), ?_⟩
  intro p hr
  let k (s : ℝ) := τ (Φ.val (p,s))-s
  have dk : HasDerivAt k 0 0 := by simpa [k] using hr.sub (hasDerivAt_id (0:ℝ))
  have d₁ := (history_derivative Φ hf.continuous p (k 0)).scomp (0:ℝ) dk
  have d₂ := (history_derivative Φ hf.continuous p (-(0:ℝ))).scomp (0:ℝ) (hasDerivAt_id (0:ℝ)).neg
  have hd := d₁.sub d₂
  simp only [zero_smul, neg_zero, Φ.initial, neg_smul, one_smul, zero_sub, neg_neg] at hd
  simpa only [history_advance Φ hf.continuous] using hd

end TransportOkaGrauert.ScalarGeneralFlow
