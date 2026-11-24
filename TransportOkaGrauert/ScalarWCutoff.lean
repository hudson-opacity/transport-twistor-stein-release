import TransportOkaGrauert.ScalarWPrimitive
import TransportOkaGrauert.ScalarReachableTrace

/-! # Two applications of the localized transverse ray operator

Multiplying before and after the angular integral gives an operator that can
be represented by a smooth kernel on the entire disk. On the inner ball the
cutoff is identically one, so its derivatives leave the transport equations
unchanged. -/
noncomputable section
namespace TransportOkaGrauert.ScalarWPrimitive
open Complex Metric Filter Set
open SimpleDiskTarget JacobiEnlargement GeodesicFlowExtension ScalarRayPairing ScalarGeneralTransport
open ScalarGeneralReduction ChartCoefficients ScalarHilbertParametrix ScalarReachableTrace
open scoped ContDiff Topology

def cut {σ : ℂ → ℝ} (F : Flow σ) (W : Window F) (χ a : ℂ → ℝ) (z : ℂ) : ℝ :=
  χ z * Wvalue σ F W.T (fun y => χ y * a y) z

theorem Wvalue_smooth {σ : ℂ → ℝ} (simple : SimpleMetric σ) (F : Flow σ) (W : Window F)
    {a : ℂ → ℝ} (sa : ContDiff ℝ ∞ a) (off : ∀ z, 1 < ‖z‖ → a z = 0) :
    ContDiff ℝ ∞ (Wvalue σ F W.T a) := by
  obtain ⟨u,su,_,mean,_⟩ := primitive simple F W a sa off
  have eq : Wvalue σ F W.T a = reCLM ∘ coefficient u 0 := by
    funext z
    simp [mean]
  rw [eq]
  exact reCLM.contDiff.comp (smooth_coefficient su 0)

theorem cut_smooth {σ : ℂ → ℝ} (simple : SimpleMetric σ) (F : Flow σ) (W : Window F)
    {χ a : ℂ → ℝ} (sχ : ContDiff ℝ ∞ χ) (off : ∀ z, 1 < ‖z‖ → χ z = 0)
    (sa : ContDiff ℝ ∞ a) : ContDiff ℝ ∞ (cut F W χ a) :=
  sχ.mul (Wvalue_smooth simple F W (sχ.mul sa) fun z hz => by simp [off z hz])

theorem cutoff_parametrix {σ : ℂ → ℝ} (simple : SimpleMetric σ) (F : Flow σ) (W : Window F)
    {r : ℝ} (hr : r ≤ 1) {χ : ℂ → ℝ} (sχ : ContDiff ℝ ∞ χ)
    (off : ∀ z, 1 < ‖z‖ → χ z = 0) (one : ∀ z ∈ ball (0:ℂ) r, χ z = 1)
    (f : ℂ → ℝ) (sf : ContDiff ℝ ∞ f) :
    Reachable σ r (fun z => ((f z + cut F W χ (cut F W χ f) z : ℝ) : ℂ)) := by
  let a := fun z => χ z * f z
  let b := fun z => χ z * cut F W χ f z
  have sa : ContDiff ℝ ∞ a := sχ.mul sf
  have sb : ContDiff ℝ ∞ b := sχ.mul (cut_smooth simple F W sχ off sf)
  obtain ⟨u,su,xu,meanU,gap⟩ := primitive simple F W a sa (fun z hz => by simp [a,off z hz])
  obtain ⟨v,sv,xv,meanV,_⟩ := primitive simple F W b sb (fun z hz => by simp [b,off z hz])
  obtain ⟨h,sh,mean,inv⟩ := correction σ (fun z => (a z : ℂ)) (ofRealCLM.contDiff.comp sa)
    u v su sv (fun z _ => gap z)
  refine ⟨h,sh,?_,?_⟩
  · intro z hz
    have hz₁ : z ∈ PencilLifts.disk := ball_subset_ball hr hz
    apply inv z hz₁ (xu z hz₁)
    have eq : (fun y => (b y : ℂ)) =ᶠ[𝓝 z] coefficient u 0 := by
      filter_upwards [isOpen_ball.mem_nhds hz] with y hy
      simp [b,cut,one y hy,meanU,a]
    intro w
    rw [xv z hz₁,perp,perp,eq.fderiv_eq]
  · intro z hz
    rw [mean z (ball_subset_ball hr hz),meanV]
    simp [a,b,cut,one z hz]
end TransportOkaGrauert.ScalarWPrimitive
