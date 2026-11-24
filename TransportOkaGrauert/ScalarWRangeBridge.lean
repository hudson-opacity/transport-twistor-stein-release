import TransportOkaGrauert.CompactNormalAlternative
import TransportOkaGrauert.ScalarReachableHilbert

/-! # The compact squared geodesic error and the scalar range -/
noncomputable section
namespace TransportOkaGrauert.ScalarWRangeBridge
open ScalarDiskHilbert ScalarReachableHilbert SimpleDiskTarget Set Metric MeasureTheory
open scoped ContDiff Topology

/-- A two-step correction by the cut-off geodesic error yields an attainable mean. -/
def Param (σ : ℂ → ℝ) (r : ℝ) (L : H →L[ℝ] H) : Prop :=
  ∀ x ∈ smooth, x + L (L x) ∈ reachable σ r

/-- A correction constructed on smooth functions induces the same correction on Hilbert classes. -/
theorem param_of_cut {σ : ℂ → ℝ} {r : ℝ} {L : H →L[ℝ] H} (cut : (ℂ → ℝ) → ℂ → ℝ)
    (sc : ∀ f, ContDiff ℝ ∞ f → ContDiff ℝ ∞ (cut f))
    (rep : ∀ f (sf : ContDiff ℝ ∞ f), L (ofSmooth f sf) = ofSmooth (cut f) (sc f sf))
    (solve : ∀ f, ContDiff ℝ ∞ f →
      ScalarReachableTrace.Reachable σ r (fun z => ((f z + cut (cut f) z : ℝ) : ℂ))) :
    Param σ r L := by
  rintro x hx
  obtain ⟨f,sf,rfl⟩ := (mem_smooth_iff _).mp hx
  rw [rep f sf,rep (cut f) (sc f sf)]
  have sc₂ := sc (cut f) (sc f sf)
  have he : ofSmooth (f+cut (cut f)) (sf.add sc₂) = ofSmooth f sf + ofSmooth _ sc₂ := by
    apply Lp.ext
    exact (ofSmooth_coeFn _ _).trans (((ofSmooth_coeFn f sf).add (ofSmooth_coeFn _ sc₂)).symm.trans
      (Lp.coeFn_add _ _).symm)
  rw [← he]
  exact ofSmooth_mem _ (solve f sf)

/-- Solving modulo the square of one compact smooth error yields every smooth real mean. -/
theorem smooth_range {σ : ℂ → ℝ} (simple : SimpleMetric σ) {r : ℝ} (hr : 0 < r) (hr₁ : r < 1)
    (L : H →L[ℝ] H) (compact : ∃ C : Set H, IsCompact C ∧ L '' closedBall 0 1 ⊆ C)
    (reg : ∀ x, L x ∈ smooth) (adjReg : ∀ x, L.adjoint x ∈ smooth)
    (solve : Param σ r L) : reachable σ r = smooth := by
  apply NormalFredholm.smooth_range smooth (reachable σ r) _ smooth_dense (L.comp L)
  · obtain ⟨C,hC,hL⟩ := compact
    exact ⟨L '' C,hC.image L.continuous,fun _ ⟨x,hx,e⟩ => ⟨L x,hL ⟨x,hx,rfl⟩,e⟩⟩
  · exact fun x => reg (L x)
  · rw [ContinuousLinearMap.adjoint_comp]
    exact fun x => adjReg (L.adjoint x)
  · exact solve
  · exact annihilator simple hr hr₁
  · rintro x ⟨f,sf,e,_⟩
    exact (mem_smooth_iff _).mpr ⟨f,sf,e⟩

/-- Existence of a compact smooth geodesic error with attainable squared correction. -/
def HasParametrix (σ : ℂ → ℝ) (r : ℝ) : Prop :=
  ∃ L : H →L[ℝ] H, (∃ C : Set H, IsCompact C ∧ L '' closedBall 0 1 ⊆ C) ∧
    (∀ x, L x ∈ smooth) ∧ (∀ x, L.adjoint x ∈ smooth) ∧ Param σ r L

theorem local_mean (h : ∀ σ : ℂ → ℝ, SimpleMetric σ → ∀ r : ℝ, 0 < r → r < 1 → HasParametrix σ r) :
    SteinMomentBridge.LocalMeanStatement := by
  apply ScalarReachableHilbert.local_mean
  intro σ simple r hr hr₁
  obtain ⟨L,compact,reg,adjReg,solve⟩ := h σ simple r hr hr₁
  exact (smooth_range simple hr hr₁ L compact reg adjReg solve).ge

/-- The same scalar parametrix proves the chart and intrinsic Stein statements for all simple disks. -/
theorem stein (h : ∀ σ : ℂ → ℝ, SimpleMetric σ → ∀ r : ℝ, 0 < r → r < 1 → HasParametrix σ r) :
    ChartStein.GeneralSimpleSurfaceStatement ∧ ManifoldStein.GeneralManifoldStatement := by
  have mean := local_mean h
  have chart : ChartStein.GeneralSimpleSurfaceStatement := fun _ hs =>
    SteinMomentBridge.chart_of_mean hs (SteinMomentBridge.mean_from_local mean hs)
  exact ⟨chart,ManifoldStein.manifold_of_chart chart⟩

end TransportOkaGrauert.ScalarWRangeBridge
