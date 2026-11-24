import TransportOkaGrauert.ScalarDiskHilbert
import TransportOkaGrauert.SmoothPathComposition
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli

/-! # Smooth integral kernels on the Euclidean unit disk

The kernel rows vary smoothly in the disk Hilbert space. Their scalar products
with the unit ball of that space form an equicontinuous bounded family on the
closed disk, giving compactness of the integral operator by Arzelà–Ascoli.
-/

noncomputable section
namespace TransportOkaGrauert.ScalarDiskHilbert
open MeasureTheory Set Metric Filter ContinuousMap
open scoped ContDiff Topology InnerProductSpace BoundedContinuousFunction ENNReal

private abbrev D := closedBall (0 : ℂ) 1
private instance : CompactSpace D := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)

private def retractDisk : C(ℂ,D) where
  toFun x := ⟨(max 1 ‖x‖)⁻¹ • x, by
    rw [mem_closedBall_zero_iff,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (lt_max_of_lt_left zero_lt_one))]
    rw [inv_mul_le_iff₀ (lt_max_of_lt_left zero_lt_one),mul_one]
    exact le_max_right _ _⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact ((continuous_const.max continuous_norm).inv₀ (fun x => (lt_max_of_lt_left zero_lt_one).ne')).smul continuous_id

private theorem retract_mem (x : ℂ) (hx : x ∈ ball 0 1) : (retractDisk x : ℂ) = x := by
  change (max 1 ‖x‖)⁻¹ • x = x
  simp [max_eq_left (mem_ball_zero_iff.mp hx).le]

private def extendDisk : (D →ᵇ ℝ) →L[ℝ] (ℂ →ᵇ ℝ) where
  toFun f := f.compContinuous retractDisk
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := BoundedContinuousFunction.continuous_compContinuous _

private def liftDisk : (D →ᵇ ℝ) →L[ℝ] H :=
  (BoundedContinuousFunction.toLp 2 μ ℝ).comp extendDisk

private theorem liftDisk_ae (f : D →ᵇ ℝ) :
    (liftDisk f : ℂ → ℝ) =ᵐ[μ] fun x => f (retractDisk x) :=
  BoundedContinuousFunction.coeFn_toLp _ _ _ _

private def constPath : ℂ →L[ℝ] C(D,ℂ × ℂ) :=
  LinearMap.mkContinuous
    { toFun := fun z => ContinuousMap.const D (z,0)
      map_add' := fun _ _ => by ext <;> simp
      map_smul' := fun _ _ => by ext <;> simp } 1 (fun z => by
        rw [one_mul]
        exact (ContinuousMap.norm_le _ (norm_nonneg z)).mpr fun _ => by simp)

private def verticalPath : C(D,ℂ × ℂ) := ⟨fun x => (0,x.1),continuous_const.prodMk continuous_subtype_val⟩

private def boundedDisk := (linearIsometryBoundedOfCompact D ℝ ℝ).toLinearIsometry.toContinuousLinearMap

/-- The row of an ambient smooth kernel as an element of real disk L². -/
def kernelRow (k : ℂ × ℂ → ℝ) (hk : ContDiff ℝ ∞ k) (x : ℂ) : H :=
  liftDisk (boundedDisk ((⟨k,hk.continuous⟩ : C(ℂ × ℂ,ℝ)).comp (constPath x + verticalPath)))

theorem kernelRow_smooth (k : ℂ × ℂ → ℝ) (hk : ContDiff ℝ ∞ k) : ContDiff ℝ ∞ (kernelRow k hk) :=
  (liftDisk.contDiff.comp boundedDisk.contDiff).comp
    ((SmoothPathComposition.smooth k hk).comp (constPath.contDiff.add contDiff_const))

theorem kernelRow_ae (k : ℂ × ℂ → ℝ) (hk : ContDiff ℝ ∞ k) (x : ℂ) :
    (kernelRow k hk x : ℂ → ℝ) =ᵐ[μ] fun y => k (x,y) := by
  apply (liftDisk_ae _).trans
  filter_upwards [ae_mem_disk] with y hy
  change k ((x,0)+(0,(retractDisk y : ℂ))) = k (x,y)
  simp [retract_mem _ hy]

private def values (s : ℂ → H) (hs : Continuous s) (f : H) : D →ᵇ ℝ :=
  boundedDisk ⟨fun x => ⟪s x.1,f⟫_ℝ,(hs.comp continuous_subtype_val).inner continuous_const⟩

private def valuesL (s : ℂ → H) (hs : Continuous s) : H →L[ℝ] (D →ᵇ ℝ) := by
  let bound := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn hs.continuousOn
  let M := bound.choose
  have hM := bound.choose_spec
  exact LinearMap.mkContinuous
    { toFun := values s hs
      map_add' := fun f g => BoundedContinuousFunction.ext (fun x => by
        change ⟪s x.1,f+g⟫_ℝ = ⟪s x.1,f⟫_ℝ + ⟪s x.1,g⟫_ℝ
        exact inner_add_right _ _ _)
      map_smul' := fun c f => BoundedContinuousFunction.ext (fun x => by
        change ⟪s x.1,c • f⟫_ℝ = c*⟪s x.1,f⟫_ℝ
        exact real_inner_smul_right _ _ _) }
    (max 0 M) (fun f => by
      apply (BoundedContinuousFunction.norm_le (mul_nonneg (le_max_left _ _) (norm_nonneg _))).mpr
      intro x
      exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right ((hM x.1 x.2).trans (le_max_right _ _)) (norm_nonneg _)))

/-- The real integral operator associated to a smooth kernel. -/
def kernelOperator (k : ℂ × ℂ → ℝ) (hk : ContDiff ℝ ∞ k) : H →L[ℝ] H :=
  liftDisk.comp (valuesL (kernelRow k hk) (kernelRow_smooth k hk).continuous)

private theorem value_eq (s : ℂ → H) (hs : Continuous s) (f : H) (x : D) :
    valuesL s hs f x = ⟪s x.1,f⟫_ℝ := by
  rfl

private theorem kernelOperator_ae_inner (k : ℂ × ℂ → ℝ) (hk : ContDiff ℝ ∞ k) (f : H) :
    (kernelOperator k hk f : ℂ → ℝ) =ᵐ[μ] fun x => ⟪kernelRow k hk x,f⟫_ℝ := by
  apply (liftDisk_ae _).trans
  filter_upwards [ae_mem_disk] with x hx
  change valuesL (kernelRow k hk) _ f (retractDisk x) = _
  rw [value_eq,retract_mem _ hx]

theorem kernelOperator_ae (k : ℂ × ℂ → ℝ) (hk : ContDiff ℝ ∞ k) (f : H) :
    (kernelOperator k hk f : ℂ → ℝ) =ᵐ[μ] fun x => ∫ y, k (x,y)*f y ∂μ := by
  apply (kernelOperator_ae_inner k hk f).trans
  apply Eventually.of_forall
  intro x
  change ⟪kernelRow k hk x,f⟫_ℝ = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [kernelRow_ae k hk x] with y hy
  change f y * (kernelRow k hk x y) = _
  rw [hy,mul_comm]

theorem kernelOperator_smooth (k : ℂ × ℂ → ℝ) (hk : ContDiff ℝ ∞ k) (f : H) :
    kernelOperator k hk f ∈ smooth := by
  refine ⟨_,(kernelRow_smooth k hk).inner ℝ (contDiff_const (c := f)),Lp.ext ?_⟩
  exact (ofSmooth_coeFn _ _).trans (kernelOperator_ae_inner k hk f).symm

private theorem kernelIntegral_eq_inner (k : ℂ × ℂ → ℝ) (hk : ContDiff ℝ ∞ k)
    (f : ℂ → ℝ) (hf : ContDiff ℝ ∞ f) (x : ℂ) :
    (∫ y, k (x,y)*f y ∂μ) = ⟪kernelRow k hk x,ofSmooth f hf⟫_ℝ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [kernelRow_ae k hk x,ofSmooth_coeFn f hf] with y hy hy'
  change k (x,y)*f y = ofSmooth f hf y * kernelRow k hk x y
  rw [hy,hy',mul_comm]

theorem kernelIntegral_smooth (k : ℂ × ℂ → ℝ) (hk : ContDiff ℝ ∞ k)
    (f : ℂ → ℝ) (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (fun x => ∫ y, k (x,y)*f y ∂μ) := by
  simp_rw [kernelIntegral_eq_inner k hk f hf]
  exact (kernelRow_smooth k hk).inner ℝ contDiff_const

/-- Restriction to the disk intertwines the ambient smooth integral formula and
the Hilbert space operator. -/
theorem kernelOperator_ofSmooth (k : ℂ × ℂ → ℝ) (hk : ContDiff ℝ ∞ k)
    (f : ℂ → ℝ) (hf : ContDiff ℝ ∞ f) :
    kernelOperator k hk (ofSmooth f hf) = ofSmooth (fun x => ∫ y, k (x,y)*f y ∂μ) (kernelIntegral_smooth k hk f hf) := by
  apply Lp.ext
  apply (kernelOperator_ae_inner k hk _).trans
  apply EventuallyEq.trans _ (ofSmooth_coeFn _ _).symm
  exact Eventually.of_forall fun x => (kernelIntegral_eq_inner k hk f hf x).symm

/-- The image of the closed unit ball is contained in a compact subset of disk L². -/
theorem kernelOperator_compact (k : ℂ × ℂ → ℝ) (hk : ContDiff ℝ ∞ k) :
    ∃ C : Set H, IsCompact C ∧ kernelOperator k hk '' closedBall 0 1 ⊆ C := by
  let s := kernelRow k hk
  have hs := (kernelRow_smooth k hk).continuous
  let T := valuesL s hs
  let A := T '' closedBall (0 : H) 1
  obtain ⟨M,hM⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn hs.continuousOn
  have bdd (f : D →ᵇ ℝ) (x : D) (hf : f ∈ A) : f x ∈ closedBall (0 : ℝ) M := by
    obtain ⟨g,hg,rfl⟩ := hf
    rw [mem_closedBall_zero_iff,value_eq]
    exact (norm_inner_le_norm _ _).trans ((mul_le_of_le_one_right (norm_nonneg _) (mem_closedBall_zero_iff.mp hg)).trans (hM x.1 x.2))
  have equi : Equicontinuous ((↑) : A → D → ℝ) := by
    intro x
    apply Metric.equicontinuousAt_iff_right.mpr
    intro ε hε
    have h : ContinuousAt (fun y : D => s y.1) x := (hs.comp continuous_subtype_val).continuousAt
    filter_upwards [h (ball_mem_nhds _ hε)] with y hy
    rintro ⟨_,g,hg,rfl⟩
    change dist (T g x) (T g y) < ε
    rw [dist_eq_norm_sub,value_eq,value_eq,← inner_sub_left]
    apply (norm_inner_le_norm _ _).trans_lt
    apply (mul_le_of_le_one_right (norm_nonneg _) (mem_closedBall_zero_iff.mp hg)).trans_lt
    have d : dist (s y.1) (s x.1) < ε := hy
    rwa [dist_comm,dist_eq_norm_sub] at d
  have hc := BoundedContinuousFunction.arzela_ascoli _ (isCompact_closedBall (0 : ℝ) M) A bdd equi
  refine ⟨liftDisk '' closure A,hc.image liftDisk.continuous,?_⟩
  rintro _ ⟨f,hf,rfl⟩
  exact ⟨T f,subset_closure ⟨f,hf,rfl⟩,rfl⟩

private theorem weighted_integrable (k : ℂ × ℂ → ℝ) (hk : Continuous k) (f g : H) :
    Integrable (fun p : ℂ × ℂ => k p * (f p.1 * g p.2)) (μ.prod μ) := by
  obtain ⟨M,hM⟩ := ((isCompact_closedBall (0 : ℂ) 1).prod (isCompact_closedBall (0 : ℂ) 1)).exists_bound_of_continuousOn hk.continuousOn
  apply ((MemLp.integrable (by norm_num : (1:ℝ≥0∞) ≤ 2) (Lp.memLp f)).mul_prod
    (MemLp.integrable (by norm_num : (1:ℝ≥0∞) ≤ 2) (Lp.memLp g))).bdd_mul hk.aestronglyMeasurable (c := M)
  have mem : ∀ᵐ p ∂μ.prod μ, p ∈ ball (0:ℂ) 1 ×ˢ ball (0:ℂ) 1 := by
    apply (Measure.ae_prod_mem_iff_ae_ae_mem (measurableSet_ball.prod measurableSet_ball)).mpr
    exact ae_mem_disk.mono (fun x hx => ae_mem_disk.mono fun y hy => ⟨hx,hy⟩)
  exact mem.mono fun p hp => hM _ ⟨ball_subset_closedBall hp.1,ball_subset_closedBall hp.2⟩

private theorem pairing (k : ℂ × ℂ → ℝ) (hk : ContDiff ℝ ∞ k) (f g : H) :
    ⟪kernelOperator k hk f,g⟫_ℝ = ∫ x, ∫ y, k (x,y)*(g x*f y) ∂μ ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [kernelOperator_ae k hk f] with x hx
  change g x * (kernelOperator k hk f x) = _
  rw [hx,← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall (fun y => by ring)

/-- Transposing the two kernel variables gives the Hilbert adjoint. -/
theorem kernelOperator_adjoint (k : ℂ × ℂ → ℝ) (hk : ContDiff ℝ ∞ k) :
    (kernelOperator k hk).adjoint = kernelOperator (k ∘ Prod.swap) (hk.comp (contDiff_snd.prodMk contDiff_fst)) := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro f g
  rw [← real_inner_comm f (kernelOperator k hk g),pairing,pairing]
  have h := integral_integral_swap (f := fun x y => k (x,y)*(f x*g y)) (weighted_integrable k hk.continuous f g)
  rw [h]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro x
  apply integral_congr_ae
  exact Eventually.of_forall (fun y => by simp [mul_comm])

theorem kernelOperator_adjoint_smooth (k : ℂ × ℂ → ℝ) (hk : ContDiff ℝ ∞ k) (f : H) :
    (kernelOperator k hk).adjoint f ∈ smooth := by
  rw [kernelOperator_adjoint]
  exact kernelOperator_smooth _ _ _

end TransportOkaGrauert.ScalarDiskHilbert
