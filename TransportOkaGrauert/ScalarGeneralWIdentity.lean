import TransportOkaGrauert.ScalarGeneralWIntegral
import TransportOkaGrauert.ScalarGeneralWDensity

/-! # The actual smooth area kernel of the perpendicular-ray average

For any two compact subsets of the interior disk one smooth ambient kernel
acts on every supported smooth input, at every prescribed center and for every
complete extension and escape time. The area measure is Euclidean and the
angular average carries the factor `-1 / (2π)`.
-/

noncomputable section
namespace TransportOkaGrauert.ScalarGeneralKernel
open Complex Metric Set Filter MeasureTheory SimpleDiskTarget JacobiEnlargement ScalarNormalLift
open scoped ContDiff Topology Interval

/-- A smooth ambient Euclidean-area kernel for the actual normalized W operator
on each compact product of centers and source supports. -/
theorem Wvalue_kernel {σ : ℂ → ℝ} (simple : SimpleMetric σ) {A B : Set ℂ}
    (hA : IsCompact A) (hB : IsCompact B)
    (inA : A ⊆ ball (0:ℂ) 1) (inB : B ⊆ ball (0:ℂ) 1) :
    ∃ K : ℂ × ℂ → ℝ, ContDiff ℝ ∞ K ∧ ∀ (F : Flow σ) (T : ℝ), 0 < T → Escapes F T →
      ∀ g : ℂ → ℝ, ContDiff ℝ ∞ g → (∀ z ∉ B, g z = 0) → ∀ a ∈ A,
        ScalarWPrimitive.Wvalue σ F T g a = ∫ y in ball (0:ℂ) 1, K (a,y)*g y := by
  obtain ⟨E,L,W,sE,sW,fam,formula,diagonal⟩ := compact_smooth_angular_kernel simple hA hB inA inB
  let K (p : ℂ × ℂ) := -(1/(2*Real.pi)) * (Real.exp (2*σ p.2)*W p)
  have sK : ContDiff ℝ ∞ K := contDiff_const.mul ((contDiff_const.mul (simple.smooth.comp contDiff_snd)).exp.mul sW)
  refine ⟨K,sK,?_⟩
  intro F T hT escape g sg off a ha
  have ha' := mem_ball_zero_iff.mp (inA ha)
  obtain ⟨C,ce,cl⟩ := fam a (inA ha)
  have atC (y : ℂ) (hy : y ∈ B) (ne : a ≠ y) :
      W (a,y) = fderiv ℝ (alpha σ E) (a,C.logMap y) (0,I*C.logMap y) /
        (‖C.logMap y‖^2*(alpha σ E (a,C.logMap y))^3) := by
    rw [cl]
    exact formula a ha y hy ne
  obtain ⟨b,h,sb,sh,pt⟩ := angular_test simple ha' C sE ce F hB inB atC g sg off
  let P (q : ℝ × ℝ) := F.val ((a,q.1),q.2)
  have cP : Continuous P := F.smooth.continuous.comp ((continuous_const.prodMk continuous_fst).prodMk continuous_snd)
  let u (q : ℝ × ℝ) := perpendicularSource σ g (P q)
  let v (q : ℝ × ℝ) := spatialWeight C E W g (P q).1
  have cv := weight_continuous simple C sE sW hB.isClosed inB sg off
  have polar := integrate_angular_test u v ((smooth_source simple.smooth sg).continuous.comp cP)
    (cv.comp (continuous_fst.comp cP)) sb sh pt hT
  have weightOff (z : ℂ) (hz : 1 ≤ ‖z‖) : spatialWeight C E W g z = 0 := by
    simp [spatialWeight,off z (fun h => (mem_ball_zero_iff.mp (inB h)).not_ge hz)]
  have area := forward_eq_area_real simple ha' C F hT escape _ cv weightOff
  change (∫ θ in (0:ℝ)..2*Real.pi, ∫ r in (0:ℝ)..T, v (θ,r)) = _ at area
  change -(1/(2*Real.pi)) * (∫ θ in (0:ℝ)..2*Real.pi, ∫ r in (0:ℝ)..T, u (θ,r)) = _
  rw [polar,area,← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_ball
  intro y hy
  change -(1/(2*Real.pi)) * (C.density y * spatialWeight C E W g y) = K (a,y)*g y
  rw [density_spatialWeight simple sE ha' C ce (fun h => diagonal a ⟨ha,h⟩) off hy]
  dsimp [K]
  ring

end TransportOkaGrauert.ScalarGeneralKernel
