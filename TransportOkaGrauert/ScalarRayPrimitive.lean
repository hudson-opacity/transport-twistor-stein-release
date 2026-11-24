import TransportOkaGrauert.JacobiEnlargement
import TransportOkaGrauert.ScalarGeneralFlow
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! # The zero-data transport primitive of the scalar ray transform

Integration forward to a fixed time beyond the exit avoids differentiating
the glancing exit time. Vanishing exterior-to-exterior ray integrals then
give a smooth primitive supported over the closed disk.
-/
noncomputable section
namespace TransportOkaGrauert.ScalarRayPrimitive
open JacobiEnlargement GeodesicFlowExtension ScalarGeneralFlow SimpleDiskTarget
open PathContinuation Set Metric Filter MeasureTheory Complex
open scoped ContDiff Topology Interval

variable {σ : ℂ → ℝ}

/-- Ray integrals of a base function along the complete convex extension. -/
def ray (F : Flow σ) (f : ℂ → ℝ) (p : State) (t : ℝ) : ℝ :=
  ∫ s in 0..t, f (F.base p s)

theorem exists_supported_primitive (simple : SimpleMetric σ) (F : Flow σ) {f : ℂ → ℝ}
    (hf : ContDiff ℝ ∞ f) (off : ∀ z, 1 < ‖z‖ → f z = 0)
    (null : ∀ p t, 0 < t → 1 < ‖p.1‖ → 1 < ‖F.base p t‖ → ray F f p t = 0) :
    ∃ u : State → ℝ, ContDiff ℝ ∞ u ∧
      (∀ p a, Circle.exp a = 1 → u (p+(0,a)) = u p) ∧
      (∀ p, 1 < ‖p.1‖ → u p = 0) ∧
      ∀ p, fderiv ℝ u p (chartVector σ p) = f p.1 := by
  let Φ : SmoothFlow State := ⟨F.val,F.smooth,F.initial,F.group⟩
  obtain ⟨T,hT,R,hR,_,out⟩ := F.uniform_escape simple
  let b : ContDiffBump (0:ℂ) := ⟨(1+R)/2,R,by linarith,by linarith⟩
  let g : State → ℝ := fun p => f p.1
  have hg : ContDiff ℝ ∞ g := hf.comp contDiff_fst
  let U (p : State) := history Φ g (p,-T)
  have hU : ContDiff ℝ ∞ U := (history_smooth Φ hg).comp (contDiff_id.prodMk contDiff_const)
  let u (p : State) := b p.1 * U p
  have hu : ContDiff ℝ ∞ u := (b.contDiff.comp contDiff_fst).mul hU
  have Ueq (p : State) : U p = -ray F f p T := by
    change (∫ t in (0:ℝ)..-T, (fun s => f (F.base p s)) (-t)) = _
    calc
      _ = ∫ t in T..0, f (F.base p t) := by
        simpa only [neg_neg,neg_zero] using
          (intervalIntegral.integral_comp_neg (fun s => f (F.base p s)) (a := 0) (b := -T))
      _ = _ := intervalIntegral.integral_symm 0 T
  have uz (p : State) (hp : 1 < ‖p.1‖) : u p = 0 := by
    by_cases h : ‖p.1‖ ≤ R
    · simp [u,Ueq,null p T hT hp (hR.trans (out p h))]
    · have hb := b.zero_of_le_dist (x := p.1) (by simpa [b] using (le_of_not_ge h))
      simp [u,hb]
  refine ⟨u,hu,?_,uz,?_⟩
  · intro p a ha
    have e : ray F f (p+(0,a)) T = ray F f p T := by
      unfold ray
      apply intervalIntegral.integral_congr
      intro t _
      simp [Flow.base,F.periodic p a ha]
    simp [u,Ueq,e]
  intro p
  by_cases h : ‖p.1‖ ≤ 1
  · have b1 : (fun q : State => b q.1) =ᶠ[𝓝 p] fun _ => (1:ℝ) :=
      continuous_fst.continuousAt.tendsto.eventually (b.eventuallyEq_one_of_mem_ball
        (x := p.1) (by simp only [mem_ball,dist_zero_right]; change ‖p.1‖ < (1+R)/2; linarith))
    have ueq : u =ᶠ[𝓝 p] U := b1.mono fun y hy => by simp [u,hy]
    have flow := (hU.differentiable (by simp) (F.val (p,0))).hasFDerivAt.comp_hasDerivAt 0 (F.ode p 0)
    rw [F.initial] at flow
    have shift (t : ℝ) : U (F.val (p,t)) = history Φ g (p,-T-t) - history Φ g (p,-t) :=
      history_advance Φ hg.continuous p t (-T)
    have d₁ := (history_derivative Φ hg.continuous p (-T-0)).scomp 0
      (by simpa using (hasDerivAt_const (0:ℝ) (-T)).sub (hasDerivAt_id 0) :
        HasDerivAt (fun t : ℝ => -T-t) (-1) 0)
    have d₂ := (history_derivative Φ hg.continuous p (-0)).scomp 0 (by simpa using (hasDerivAt_id (0:ℝ)).neg : HasDerivAt (fun t : ℝ => -t) (-1) 0)
    have dshift := d₁.sub d₂
    have v : F.val (p,0) = p := F.initial p
    have fr (y : State) (e : F.factor =ᶠ[𝓝 y.1] σ) : chartVector F.factor y = chartVector σ y := by
      simp [chartVector,Isothermal.angularDrift,e.eq_of_nhds,e.fderiv_eq]
    have hz := off (F.base p T) (hR.trans (out p (h.trans hR.le)))
    rw [ueq.fderiv_eq,← fr p (F.germ h)]
    have deriv : HasDerivAt (fun t => U (F.val (p,t))) (f p.1) 0 := by
      rw [funext shift]
      change f (F.val (p,T)).1 = 0 at hz
      simpa [Function.comp_def,Φ,g,F.initial,hz] using dshift
    exact flow.unique deriv
  · have ho := lt_of_not_ge h
    have e : u =ᶠ[𝓝 p] fun _ => 0 :=
      (continuous_fst.norm.continuousAt.eventually_const_lt ho).mono fun q hq => uz q hq
    simp [e.fderiv_eq,off p.1 ho]

end TransportOkaGrauert.ScalarRayPrimitive
