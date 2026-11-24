import TransportOkaGrauert.PhysicalStein

/-! # Physical Levi form along the zero section

The Cartesian horizontal part of `J` differs from multiplication by `i`
by a term divisible by the square of the velocity. The connection contributes
to the vertical first derivative of `J`, but the velocity barrier is critical
at zero. Thus neither correction enters the Levi form there.
-/

noncomputable section
namespace TransportOkaGrauert.PhysicalStein

open Complex ChartStein FrameLevi ConformalCollar CollarGluing Filter
open scoped ContDiff ComplexConjugate Topology

private theorem first_J_jet {σ : ℂ → ℝ} (hs : ContDiff ℝ ∞ σ) (z : ℂ) (v w : E) :
    (fderiv ℝ (J σ) (z,0) w v).1 = 0 := by
  let p : E := (z,0)
  have dj := ((J_smooth hs (p := p) (by simp [p])).differentiableAt (by simp)).hasFDerivAt
  have d := (ContinuousLinearMap.fst ℝ ℂ ℂ).hasFDerivAt.comp p
    (dj.clm_apply (hasFDerivAt_const v p))
  let B := fun y : E => conj ((J σ y v).1) - I * conj v.1
  have db : DifferentiableAt ℝ B p :=
    (conjCLE.toContinuousLinearMap.differentiableAt.comp p d.differentiableAt).sub_const _
  have eq : (fun y => (J σ y v).1) =ᶠ[𝓝 p] fun y : E => I * v.1 + y.2^2 * B y := by
    filter_upwards [(continuous_snd.norm.continuousAt (x := p)).eventually_lt_const
      (show ‖p.2‖ < 1 by simp [p])] with y hy
    have rel := congrArg Prod.fst (coframe_J σ hy v)
    simp only [coframe_apply, Prod.smul_fst, smul_eq_mul] at rel
    dsimp [B]
    linear_combination rel
  have dg := (hasFDerivAt_const (I * v.1) p).add
    (((hasFDerivAt_snd (𝕜 := ℝ) (p := p)).pow 2).mul db.hasFDerivAt)
  have he := congrArg (fun A : E →L[ℝ] ℂ => A w) (d.fderiv.symm.trans (eq.fderiv_eq.trans dg.fderiv))
  simpa [p] using he

def second {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : F → ℝ) (p v : F) := fderiv ℝ (fderiv ℝ f) p v v

/-- The Levi form of any smooth real potential whose vertical differential
vanishes at zero velocity is the sum of its two ordinary real Hessians there. -/
theorem levi_zero {σ : ℂ → ℝ} (hs : ContDiff ℝ ∞ σ) {z : ℂ} {f : E → ℝ}
    (df : ContDiffAt ℝ 2 f (z,0)) (vertical_critical : ∀ b : ℂ, fderiv ℝ f (z,0) (0,b) = 0)
    (v : E) :
    ddC (J σ) f (z,0) v (J σ (z,0) v) =
      second f (z,0) v + second f (z,0) (I • v) := by
  let p : E := (z,0)
  have dJ := ((J_smooth hs (p := p) (by simp [p])).differentiableAt (by simp)).hasFDerivAt
  have ddf := ((df.fderiv_right (m := 1) (by decide)).differentiableAt one_ne_zero).hasFDerivAt
  have dform := (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℝ) (0 : Fin 1)).hasFDerivAt.comp
    p (ddf.clm_comp dJ).neg
  change HasFDerivAt (dc (J σ) f) _ p at dform
  let w := I • v
  have jj : J σ p w = -v := by simpa only [w, ← J_zero σ z] using J_sq σ (p := p) (by simp [p]) v
  have rem0 : (0 : Fin 2).removeNth ![v,w] = ![w] := by funext i; fin_cases i; rfl
  have rem1 : (1 : Fin 2).removeNth ![v,w] = ![v] := by funext i; fin_cases i; rfl
  have kill (u t : E) : fderiv ℝ f p (fderiv ℝ (J σ) p u t) = 0 := by
    have e := first_J_jet hs z t u
    have zero : fderiv ℝ (J σ) p u t = (0,(fderiv ℝ (J σ) p u t).2) := Prod.ext e rfl
    rw [zero, vertical_critical]
  rw [J_zero]
  change ddC (J σ) f p v w = _
  have component (t s : E) : fderiv ℝ (fun x => dc (J σ) f x ![t]) p s =
      -(fderiv ℝ f p (fderiv ℝ (J σ) p s t) + fderiv ℝ (fderiv ℝ f) p s (J σ p t)) := by
    have d := (ddf.clm_apply (dJ.clm_apply (hasFDerivAt_const t p))).neg
    change HasFDerivAt (fun x => dc (J σ) f x ![t]) _ p at d
    rw [d.fderiv]
    simp [p]
  rw [ddC, extDeriv_apply dform.differentiableAt]
  simp only [Nat.reduceAdd, Fin.sum_univ_two, rem0, rem1, Fin.val_zero, Fin.val_one,
    pow_zero, pow_one, one_smul, neg_one_smul, Matrix.cons_val_zero, Matrix.cons_val_one]
  simp only [component, neg_neg]
  rw [kill, kill, jj, map_neg, zero_add, zero_add, neg_neg]
  rw [J_zero σ z]
  rfl

private def barrier (L : ℝ) (z : ℂ) : ℝ := -Real.log (defining L z)

private theorem barrier_smooth {L : ℝ} {z : ℂ} (hz : defining L z ≠ 0) :
    ContDiffAt ℝ ∞ (barrier L) z :=
  ((smooth_defining L).contDiffAt.log hz).neg

private theorem barrier_slope {L : ℝ} {z : ℂ} (hz : defining L z ≠ 0) (v : ℂ) :
    fderiv ℝ (barrier L) z v = -(fderiv ℝ (defining L) z v) / defining L z := by
  have d := (((smooth_defining L).differentiable (by simp) z).hasFDerivAt.log hz).neg
  rw [show fderiv ℝ (barrier L) z = _ from d.fderiv]
  simp [div_eq_inv_mul]

private theorem second_apply {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : F → ℝ} {p : F} (df : ContDiffAt ℝ 2 f p) (v : F) :
    second f p v = fderiv ℝ (fun y => fderiv ℝ f y v) p v := by
  have h := ((df.fderiv_right (m := 1) (by decide)).differentiableAt one_ne_zero).hasFDerivAt
  rw [(h.clm_apply (hasFDerivAt_const v p)).fderiv]
  simp [second]

private theorem second_barrier {L : ℝ} {z : ℂ} (hb : defining L z ≠ 0) (v : ℂ) :
    second (barrier L) z v =
      (2 * (1 - 2 * L * b₀ z) * ‖v‖ ^ 2 + 8 * L * dot z v ^ 2) / defining L z +
      (fderiv ℝ (defining L) z v / defining L z) ^ 2 := by
  have h := ((smooth_defining L).differentiable (by simp) z).hasFDerivAt
  have h' := ((((smooth_defining L).fderiv_right (m := ∞) (by simp)).differentiable (by simp) z).hasFDerivAt.clm_apply
    (hasFDerivAt_const v z))
  have d := (h'.neg.mul ((hasDerivAt_inv hb).comp_hasFDerivAt z h)).congr_of_eventuallyEq (f₁ := fun y => fderiv ℝ (barrier L) y v) (by
    filter_upwards [(smooth_defining L).continuous.continuousAt.eventually_ne hb] with y hy
    simpa only [div_eq_mul_inv] using barrier_slope hy v)
  have eq := conformalHessian_defining (fun _ => 0) L z v
  unfold conformalHessian at eq
  rw [h'.fderiv] at eq
  rw [second_apply ((barrier_smooth hb).of_le (by decide)), d.fderiv]
  simp at eq
  simp
  field_simp [hb]
  linear_combination -(defining L z) * eq

private theorem disk_eq : diskBarrier = barrier 0 := by
  funext z
  simp [diskBarrier, barrier, defining]

private theorem disk_critical (v : ℂ) : fderiv ℝ (barrier 0) 0 v = 0 := by
  have hz : defining 0 0 ≠ 0 := by simp [defining, b₀]
  rw [barrier_slope hz]
  have eq : defining 0 = fun z : ℂ => 1 - (z.re^2 + z.im^2) := by
    funext z
    simp [defining, b₀, Complex.normSq_apply, pow_two]
  rw [eq]
  have d := (hasFDerivAt_const (𝕜 := ℝ) (1 : ℝ) (0 : ℂ)).sub
    ((reCLM.hasFDerivAt.pow 2).add (imCLM.hasFDerivAt.pow 2))
  change HasFDerivAt (fun z : ℂ => 1 - (z.re^2 + z.im^2)) _ 0 at d
  rw [d.fderiv]
  simp

private theorem second_side {L : ℝ} {z : ℂ} (hb : defining L z ≠ 0) (v : E) :
    second (fun y : E => barrier 0 y.2 + barrier L y.1) (z,0) v =
      second (barrier 0) 0 v.2 + second (barrier L) z v.1 := by
  let p : E := (z,0)
  have hz : defining 0 0 ≠ 0 := by simp [defining, b₀]
  have h₁ := barrier_smooth hb
  have h₂ := barrier_smooth hz
  have d₁ := ((h₁.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)).hasFDerivAt
  have d₂ := ((h₂.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)).hasFDerivAt
  have dx := hasFDerivAt_fst (𝕜 := ℝ) (p := p)
  have dy := hasFDerivAt_snd (𝕜 := ℝ) (p := p)
  have d := ((d₂.comp p dy).clm_comp (hasFDerivAt_const (.snd ℝ ℂ ℂ) p)).add
    ((d₁.comp p dx).clm_comp (hasFDerivAt_const (.fst ℝ ℂ ℂ) p))
  have h := d.congr_of_eventuallyEq (f₁ := fderiv ℝ (fun y : E => barrier 0 y.2 + barrier L y.1)) (by
    filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds ((h₁.of_le (m := 2) (by decide)).eventually (by decide)),
      continuous_snd.continuousAt.preimage_mem_nhds ((h₂.of_le (m := 2) (by decide)).eventually (by decide))] with y hy₁ hy₂
    change ContDiffAt ℝ 2 (barrier L) y.1 at hy₁
    change ContDiffAt ℝ 2 (barrier 0) y.2 at hy₂
    exact (((ContDiffAt.differentiableAt hy₂ (by decide)).hasFDerivAt.comp y hasFDerivAt_snd).add
      ((ContDiffAt.differentiableAt hy₁ (by decide)).hasFDerivAt.comp y hasFDerivAt_fst)).fderiv)
  rw [second, h.fderiv]
  simp [p,second]

/-- Along the zero section the base collar's logarithmic branch has strictly
positive physical Levi form in every nonzero direction. The vertical coefficient
is exactly four in the Euclidean velocity coordinate. -/
theorem strict_side_zero {σ : ℂ → ℝ} (hs : ContDiff ℝ ∞ σ) {L : ℝ} (hL : 0 ≤ L)
    {z : ℂ} (hb : 0 < defining L z) (hz : 0 < 1 - 2 * L * b₀ z) :
    StrictAt (J σ) (fun y : E => diskBarrier y.2 - Real.log (defining L y.1)) (z,0) := by
  change StrictAt (J σ) (fun y : E => diskBarrier y.2 + barrier L y.1) (z,0)
  rw [disk_eq]
  let p : E := (z,0)
  have h₁ := barrier_smooth hb.ne'
  have h₂ := barrier_smooth (show defining 0 0 ≠ 0 by simp [defining, b₀])
  have df : ContDiffAt ℝ ∞ (fun y : E => barrier 0 y.2 + barrier L y.1) p :=
    (h₂.comp p contDiffAt_snd).add (h₁.comp p contDiffAt_fst)
  have critical (v : ℂ) : fderiv ℝ (fun y : E => barrier 0 y.2 + barrier L y.1) p (0,v) = 0 := by
    have d := (((h₂.differentiableAt (by simp)).hasFDerivAt.comp p (hasFDerivAt_snd (𝕜 := ℝ) (p := p))).add
      ((h₁.differentiableAt (by simp)).hasFDerivAt.comp p (hasFDerivAt_fst (𝕜 := ℝ) (p := p))))
    change HasFDerivAt (fun y : E => barrier 0 y.2 + barrier L y.1) _ p at d
    rw [d.fderiv]
    simp [disk_critical]
  have vertical (v : ℂ) : second (barrier 0) 0 v = 2 * ‖v‖^2 := by
    rw [second_barrier (by simp [defining, b₀])]
    have h := disk_critical v
    rw [barrier_slope (by simp [defining, b₀])] at h
    simp [defining, b₀] at h ⊢
    simp [h]
  have lower (v : ℂ) : 2 * (1 - 2 * L * b₀ z) * ‖v‖^2 / defining L z ≤ second (barrier L) z v := by
    rw [second_barrier hb.ne', add_div]
    linarith [div_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 8) hL) (sq_nonneg (dot z v))) hb.le,
      sq_nonneg (fderiv ℝ (defining L) z v / defining L z)]
  intro v hv
  rw [levi_zero hs (df.of_le (by decide)) critical, second_side hb.ne', second_side hb.ne',
    vertical, vertical]
  have l₁ := lower v.1
  have l₂ := lower (I • v).1
  have n₁ : 0 ≤ second (barrier L) z (I • v).1 := (by positivity : 0 ≤ 2 * (1 - 2 * L * b₀ z) *
    ‖(I • v).1‖^2 / defining L z).trans l₂
  by_cases h : v.1 = 0
  · have w : v.2 ≠ 0 := fun e => hv (Prod.ext h e)
    have n : 0 ≤ second (barrier L) z v.1 := (by positivity : 0 ≤ 2 * (1 - 2 * L * b₀ z) *
      ‖v.1‖^2 / defining L z).trans l₁
    positivity
  · have n : 0 < second (barrier L) z v.1 := lt_of_lt_of_le (by positivity) l₁
    positivity

end TransportOkaGrauert.PhysicalStein
