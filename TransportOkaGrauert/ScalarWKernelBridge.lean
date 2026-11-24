import TransportOkaGrauert.ScalarDiskKernel
import TransportOkaGrauert.ScalarWRangeBridge
import TransportOkaGrauert.ScalarWCutoff

/-! # Smooth kernel realization of the cut-off geodesic correction -/
noncomputable section
namespace TransportOkaGrauert.ScalarWRangeBridge
open ScalarDiskHilbert ScalarReachableTrace ScalarWPrimitive SimpleDiskTarget JacobiEnlargement ScalarRayPairing
open Metric Set MeasureTheory
open scoped ContDiff Topology

/-- A pointwise disk-integral formula on smooth inputs identifies their Hilbert-space images. -/
theorem represent {k : ℂ × ℂ → ℝ} (hk : ContDiff ℝ ∞ k) {f a : ℂ → ℝ}
    (hf : ContDiff ℝ ∞ f) (ha : ContDiff ℝ ∞ a)
    (h : ∀ z ∈ ball (0 : ℂ) 1, a z = ∫ y in ball (0:ℂ) 1, k (z,y)*f y) :
    kernelOperator k hk (ofSmooth f hf) = ofSmooth a ha := by
  rw [kernelOperator_ofSmooth]
  apply Lp.ext
  filter_upwards [ofSmooth_coeFn _ (kernelIntegral_smooth k hk f hf),ofSmooth_coeFn a ha,ae_mem_disk] with z e ea hz
  exact e.trans ((h z hz).symm.trans ea.symm)

/-- A smooth two-point kernel representing the cut transverse-geodesic average yields the parametrix. -/
theorem of_kernel {σ : ℂ → ℝ} (simple : SimpleMetric σ) (F : Flow σ) (W : Window F) {r : ℝ}
    (hr : r ≤ 1) (χ : ℂ → ℝ) (sχ : ContDiff ℝ ∞ χ) (off : ∀ z, 1 < ‖z‖ → χ z = 0)
    (one : ∀ z ∈ ball (0:ℂ) r, χ z = 1) (k : ℂ × ℂ → ℝ) (hk : ContDiff ℝ ∞ k)
    (h : ∀ (f : ℂ → ℝ), ContDiff ℝ ∞ f → ∀ z ∈ ball (0:ℂ) 1,
      cut F W χ f z = ∫ y in ball (0:ℂ) 1, k (z,y)*f y) : HasParametrix σ r := by
  refine ⟨kernelOperator k hk,kernelOperator_compact _ _,kernelOperator_smooth _ _,
    kernelOperator_adjoint_smooth _ _,?_⟩
  exact param_of_cut (cut F W χ) (fun _ sf => cut_smooth simple F W sχ off sf)
    (fun f sf => represent hk sf (cut_smooth simple F W sχ off sf) (h f sf))
    (cutoff_parametrix simple F W hr sχ off one)

end TransportOkaGrauert.ScalarWRangeBridge
