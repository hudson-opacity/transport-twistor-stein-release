import TransportOkaGrauert.FiniteTimeFlow
import TransportOkaGrauert.GeodesicFlowExtension

/-! # Complete smooth flow of the extended geodesic field -/

namespace TransportOkaGrauert.GlobalGeodesicFlow
noncomputable section
open Set Filter MeasureTheory SmoothLocalFlow
open scoped Topology ContDiff unitInterval NNReal
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

private theorem trajectory {X : E → E} {B : ℝ≥0} (lip : LipschitzWith B X)
    (bound : ∀ x, ‖X x‖ ≤ B) (y : E) {T : ℝ} (hT : 0 < T) :
    ∃ γ : ℝ → E, γ 0 = y ∧ ∀ r, |r| < T → HasDerivAt γ (X (γ r)) r := by
  let t₀ : Icc (-T) T := ⟨0,by simp [hT.le]⟩
  have H : IsPicardLindelof (fun _ => X) t₀ y (B * ⟨T,hT.le⟩) 0 B B :=
    .of_time_independent (fun x _ => bound x) lip.lipschitzOnWith (by simp [t₀])
  obtain ⟨γ,h0,hγ⟩ := H.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨γ,h0,fun r hr => (hγ r ⟨(abs_lt.mp hr).1.le,(abs_lt.mp hr).2.le⟩).hasDerivAt
    (Icc_mem_nhds (abs_lt.mp hr).1 (abs_lt.mp hr).2)⟩

omit [CompleteSpace E] in
private theorem on_path {X : E → E} (hX : ContDiff ℝ ∞ X) {y : E} {t : ℝ}
    {v : Path E} (sol : residual X hX ((y,t),v) = 0) {s : ℝ} (hs : s ∈ Icc (0:ℝ) 1) :
    clamped v s = y + t • ∫ r : ℝ in 0..s, X (clamped v r) := by
  have h := DFunLike.congr_fun sol (⟨s,hs⟩ : unitInterval)
  change v ⟨s,hs⟩ - y - t • (∫ r : ℝ in 0..s, X (clamped v r)) = 0 at h
  rw [clamped,projIcc_of_mem _ hs]
  exact sub_eq_iff_eq_add'.mp (sub_eq_zero.mp h)

private theorem path_deriv {X : E → E} (hX : ContDiff ℝ ∞ X) {y : E} {t : ℝ}
    {v : Path E} (sol : residual X hX ((y,t),v) = 0) {s : ℝ} (hs : s ∈ Ico (0:ℝ) 1) :
    HasDerivWithinAt (clamped v) (t • X (clamped v s)) (Ici s) s := by
  have h := hX.continuous.comp (continuous_clamped v)
  have D := intervalIntegral.integral_hasDerivAt_right (h.intervalIntegrable 0 s)
    (h.stronglyMeasurableAtFilter volume (𝓝 s)) h.continuousAt
  have D' := (D.const_smul t).const_add y
  exact (D'.hasDerivWithinAt.congr (fun _ hr => on_path hX sol hr)
    (on_path hX sol (Ico_subset_Icc_self hs))).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hs)

private theorem path_unique {X : E → E} (hX : ContDiff ℝ ∞ X) {B : ℝ≥0}
    (lip : LipschitzWith B X) {yt : E × ℝ} {u v : Path E}
    (hu : residual X hX (yt,u) = 0) (hv : residual X hX (yt,v) = 0) : u = v := by
  rcases yt with ⟨y,t⟩
  let S := ContinuousLinearMap.lsmul ℝ (E := E) ℝ t
  have eq := ODE_solution_unique_of_mem_Icc_right
    (v := fun _ e => t • X e) (s := fun _ => univ)
    (fun _ _ => (S.lipschitz.comp lip).lipschitzOnWith)
    (continuous_clamped u).continuousOn (fun _ hs => path_deriv hX hu hs) (fun _ _ => trivial)
    (continuous_clamped v).continuousOn (fun _ hs => path_deriv hX hv hs) (fun _ _ => trivial)
    (by rw [on_path hX hu (show (0:ℝ) ∈ Icc 0 1 by simp),
      on_path hX hv (show (0:ℝ) ∈ Icc 0 1 by simp)]; simp)
  ext s
  simpa only [clamped,projIcc_of_mem _ s.property] using eq s.property

private theorem path_of_curve {X : E → E} (hX : ContDiff ℝ ∞ X) {γ : ℝ → E} {T : ℝ}
    (D : ∀ r, |r| < T → HasDerivAt γ (X (γ r)) r) {t : ℝ} (ht : |t| < T) :
    ∃ v : Path E, (∀ s, v s = γ (t*s.val)) ∧ residual X hX ((γ 0,t),v) = 0 := by
  apply FiniteTimeFlow.curve_solves
  intro s hs
  apply D
  rw [abs_mul, abs_of_nonneg hs.1]
  exact (mul_le_of_le_one_right (abs_nonneg _) hs.2).trans_lt ht

/-- For a bounded smooth Lipschitz vector field there is a global flow,
jointly smooth in both initial state and elapsed time. -/
theorem exists_flow {X : E → E} (hX : ContDiff ℝ ∞ X) {B : ℝ≥0}
    (lip : LipschitzWith B X) (bound : ∀ x, ‖X x‖ ≤ B) :
    ∃ Φ : E × ℝ → E, ContDiff ℝ ∞ Φ ∧ (∀ y, Φ (y,0) = y) ∧
      (∀ y t, HasDerivAt (fun s => Φ (y,s)) (X (Φ (y,t))) t) ∧
      ∀ y t s, Φ (Φ (y,t),s) = Φ (y,t+s) := by
  have paths (yt : E × ℝ) : ∃! v : Path E, residual X hX (yt,v) = 0 := by
    obtain ⟨γ,h0,hγ⟩ := trajectory lip bound yt.1 (T := |yt.2|+1) (by positivity)
    obtain ⟨v,_,hv⟩ := path_of_curve hX hγ (t := yt.2) (by linarith)
    rw [h0] at hv
    exact ⟨v,hv,fun _ h => path_unique hX lip h hv⟩
  obtain ⟨P,smooth,sol⟩ := FiniteTimeFlow.smooth_family X hX paths
  let Φ (yt : E × ℝ) := P yt 1
  have agrees {y : E} {γ : ℝ → E} {T : ℝ} (h0 : γ 0 = y)
      (D : ∀ r, |r| < T → HasDerivAt γ (X (γ r)) r) {r : ℝ} (hr : |r| < T) :
      Φ (y,r) = γ r := by
    obtain ⟨v,ev,hv⟩ := path_of_curve hX D hr
    rw [h0] at hv
    change P (y,r) 1 = γ r
    rw [path_unique hX lip (sol (y,r)) hv,ev]
    simp
  have initial (y : E) : Φ (y,0) = y := by
    obtain ⟨γ,h0,D⟩ := trajectory lip bound y (T := 1) zero_lt_one
    exact (agrees h0 D (by norm_num)).trans h0
  have solves (y : E) (t : ℝ) : HasDerivAt (fun r => Φ (y,r)) (X (Φ (y,t))) t := by
    let T := |t|+1
    have ht : |t| < T := by dsimp [T]; linarith
    obtain ⟨γ,h0,D⟩ := trajectory lip bound y (T := T) ((abs_nonneg t).trans_lt ht)
    rw [agrees h0 D ht]
    apply (D t ht).congr_of_eventuallyEq
    filter_upwards [continuous_abs.continuousAt.eventually_lt_const ht] with r hr
    exact agrees h0 D hr
  refine ⟨Φ,(ContinuousMap.evalCLM (R := ℝ) (M := E) (1 : unitInterval)).contDiff.comp smooth,initial,solves,?_⟩
  intro y t s
  have eq := ODE_solution_unique_of_mem_Ioo (v := fun _ => X) (s := fun _ => univ)
    (a := -(|s|+1)) (b := |s|+1) (t₀ := 0) (fun _ _ => lip.lipschitzOnWith)
    (by constructor <;> linarith [abs_nonneg s])
    (fun r _ => ⟨solves (Φ (y,t)) r,trivial⟩)
    (g := fun r => Φ (y,t+r))
    (fun r _ => ⟨by
      have add : HasDerivAt (fun q : ℝ => t+q) 1 r := (hasDerivAt_id r).const_add t
      simpa only [one_smul,Function.comp_def] using (solves y (t+r)).scomp r add, trivial⟩)
    (by simp [initial])
  exact eq (x := s) (by constructor <;> linarith [le_abs_self s, neg_abs_le s])

/-- The complete modified flow is an actual geodesic of the original metric
at every state whose base point has norm less than two. -/
theorem angularFlow {lam : ℂ → ℝ} (hs : ContDiff ℝ ∞ lam) :
    ∃ Φ : (ℂ × ℝ) × ℝ → ℂ × ℝ, ContDiff ℝ ∞ Φ ∧ (∀ y, Φ (y,0) = y) ∧
      (∀ y t, HasDerivAt (fun r => Φ (y,r)) (GeodesicFlowExtension.extended lam (Φ (y,t))) t) ∧
      (∀ y t s, Φ (Φ (y,t),s) = Φ (y,t+s)) ∧
      ∀ y t, ‖(Φ (y,t)).1‖ < 2 → HasDerivAt (fun r => Φ (y,r))
        (PathContinuation.chartVector lam (Φ (y,t))) t := by
  obtain ⟨B,lip,bound⟩ := GeodesicFlowExtension.bounded_lipschitz hs
  obtain ⟨Φ,smooth,zero,D,group⟩ := exists_flow (GeodesicFlowExtension.smooth hs) lip bound
  exact ⟨Φ,smooth,zero,D,group,fun y t ht => GeodesicFlowExtension.agrees ht ▸ D y t⟩
end
end TransportOkaGrauert.GlobalGeodesicFlow
