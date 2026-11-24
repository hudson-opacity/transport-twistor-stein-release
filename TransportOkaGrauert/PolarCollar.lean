import TransportOkaGrauert.ConformalFrame
import TransportOkaGrauert.StrictJacobiWeight
import TransportOkaGrauert.SmoothJacobiFamily

/-!
# From a strict angular Jacobi inequality to the actual Levi form

A twice differentiable angular weight is lifted constantly in the velocity radius.
Continuity of its differentiated frame coefficients gives one common collar on each
compact set of directions. All frame derivatives in this result are computed.
-/

noncomputable section

namespace TransportOkaGrauert.PolarCollar

open ConformalFrame FrameLevi LeviBoundary StrictJacobiWeight Set Filter
open scoped Topology ContDiff

abbrev Direction := ℂ × ℝ

def direction : Chart →L[ℝ] Direction :=
  (ContinuousLinearMap.fst ℝ ℂ (ℝ × ℝ)).prod
    ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (.snd ℝ ℂ (ℝ × ℝ)))

private def slice (z : Direction) : Chart := (z.1,z.2,0)

def project (P : Chart → Chart) (z : Direction) : Direction := direction (P (slice z))

private def angularJet (σ : ℂ → ℝ) (h : Direction → ℝ) (z : Direction) : FrameJet where
  curvature := SimpleDiskTarget.curvature σ z.1
  x := along (project (X σ)) h z
  h := along (project (H σ)) h z
  xx := along (project (X σ)) (along (project (X σ)) h) z
  hh := along (project (H σ)) (along (project (H σ)) h) z
  vv := along (project V) (along (project V) h) z
  hv := along (project (H σ)) (along (project V) h) z
  xv := along (project (X σ)) (along (project V) h) z

private theorem project_smooth {P : Chart → Chart} (hp : ContDiff ℝ ∞ P) :
    ContDiff ℝ ∞ (project P) := direction.contDiff.comp (hp.comp (by unfold slice; fun_prop))

private theorem d_along {h : Direction → ℝ} {z : Direction} {P : Direction → Direction}
    (dh : ContDiffAt ℝ 2 h z) (dp : ContDiff ℝ ∞ P) : ContDiffAt ℝ 1 (along P h) z :=
  (dh.fderiv_right (m := 1) (by decide)).clm_apply (dp.contDiffAt.of_le (by decide))

private theorem first_lift {h : Direction → ℝ} {p : Chart} (dh : DifferentiableAt ℝ h (direction p))
    {P : Chart → Chart} (indep : ∀ y, direction (P y) = project P (direction y)) :
    along P (h ∘ direction) p = along (project P) h (direction p) := by
  unfold along
  rw [(dh.hasFDerivAt.comp p direction.hasFDerivAt).fderiv]
  simp [indep]

private theorem second_lift {h : Direction → ℝ} {p : Chart} (dh : ContDiffAt ℝ 2 h (direction p))
    {P Q : Chart → Chart} (dQ : ContDiff ℝ ∞ Q)
    (indepP : ∀ y, direction (P y) = project P (direction y))
    (indepQ : ∀ y, direction (Q y) = project Q (direction y)) :
    along P (along Q (h ∘ direction)) p =
      along (project P) (along (project Q) h) (direction p) := by
  have he : along Q (h ∘ direction) =ᶠ[𝓝 p] (along (project Q) h) ∘ direction := by
    filter_upwards [direction.continuous.continuousAt.eventually (dh.eventually (by decide))] with y hy
    exact first_lift (hy.differentiableAt (by decide)) indepQ
  have hd := (d_along dh (project_smooth dQ)).differentiableAt (by decide)
  exact (congrArg (fun L : Chart →L[ℝ] ℝ => L (P p)) he.fderiv_eq).trans (first_lift hd indepP)

private theorem jet_eq {σ : ℂ → ℝ} (hs : ContDiff ℝ ∞ σ) {h : Direction → ℝ} {p : Chart}
    (dh : ContDiffAt ℝ 2 h (direction p)) :
    jet (frame σ) (h ∘ direction) p = angularJet σ h (direction p) := by
  obtain ⟨dx, dH⟩ := smooth_XH hs
  have x : ∀ y, direction (X σ y) = project (X σ) (direction y) := fun _ => rfl
  have hh : ∀ y, direction (H σ y) = project (H σ) (direction y) := fun _ => rfl
  have v : ∀ y, direction (V y) = project V (direction y) := fun _ => rfl
  have dV : ContDiff ℝ ∞ V := contDiff_const
  simp only [jet, angularJet, frame, first_lift (dh.differentiableAt (by decide)) x,
    first_lift (dh.differentiableAt (by decide)) hh, second_lift dh dx x x, second_lift dh dH hh hh,
    second_lift dh dV v v, second_lift dh dV hh v, second_lift dh dV x v]
  rfl

private theorem continuous_jet {σ : ℂ → ℝ} (hs : ContDiff ℝ ∞ σ) {h : Direction → ℝ}
    {S : Set Direction} (dh : ∀ z ∈ S, ContDiffAt ℝ 2 h z) : ContinuousJetOn (angularJet σ h) S := by
  obtain ⟨dx,dH⟩ := smooth_XH hs
  have x := project_smooth dx
  have y := project_smooth dH
  have v : ContDiff ℝ ∞ (project V) := project_smooth contDiff_const
  have c1 {P : Direction → Direction} (dP : ContDiff ℝ ∞ P) : ContinuousOn (along P h) S :=
    fun z hz => (d_along (dh z hz) dP).continuousAt.continuousWithinAt
  have c2 {P Q : Direction → Direction} (dP : ContDiff ℝ ∞ P) (dQ : ContDiff ℝ ∞ Q) :
      ContinuousOn (along P (along Q h)) S := by
    intro z hz
    exact (((d_along (dh z hz) dQ).fderiv_right (m := 0) (by decide)).clm_apply
      (dP.contDiffAt.of_le (by decide))).continuousAt.continuousWithinAt
  have hσ' := hs.fderiv_right (m := ∞) (by simp)
  have hσ'' (v : ℂ) := ((hσ'.clm_apply (contDiff_const (c := v))).fderiv_right (m := ∞) (by simp))
  have curv : Continuous (SimpleDiskTarget.curvature σ) := by
    unfold SimpleDiskTarget.curvature SimpleDiskTarget.laplacian
    exact ((contDiff_const (c := (-2 : ℝ))).mul hs).exp.continuous.neg.mul
      ((((hσ'' 1).clm_apply contDiff_const).add ((hσ'' Complex.I).clm_apply contDiff_const)).continuous)
  exact ⟨(curv.comp continuous_fst).continuousOn,c1 x,c1 y,c2 x x,c2 y y,c2 v v,c2 y v,c2 x v⟩

/-- A compact family of directions with a strict Jacobi boundary inequality has one
velocity collar on which the genuine exterior derivative is positive definite. -/
theorem uniform_collar {σ : ℂ → ℝ} (hs : ContDiff ℝ ∞ σ) {h : Direction → ℝ} {S : Set Direction}
    (hS : IsCompact S) (dh : ∀ z ∈ S, ContDiffAt ℝ 2 h z)
    (defect : ∀ z ∈ S, 0 < along (project (X σ)) (along (project (X σ)) h) z -
      SimpleDiskTarget.curvature σ z.1 - (along (project (X σ)) h z)^2) :
    ∃ η > 0, ∀ p : Chart, direction p ∈ S → p.2.2 < 0 → t p < η →
      ∀ w : Chart, w ≠ 0 → 0 < ddC (J σ) (potential (frame σ) (h ∘ direction)) p w (J σ p w) := by
  obtain ⟨η,hη,good⟩ := uniform_schur_collar hS (angularJet σ h) (continuous_jet hs dh) defect
  refine ⟨η,hη,?_⟩
  intro p hdir hp ht w hw
  have dp := dh (direction p) hdir
  have eqs := equationsAt hs p hp
  obtain ⟨hB,hSchur⟩ := good (direction p) hdir (t p) ⟨eqs.positive,ht⟩
  rw [← jet_eq hs dp] at hB hSchur
  apply ConformalFrame.positive_of_schur hs p hp (dp.comp p direction.contDiff.contDiffAt) _ hB hSchur hw
  filter_upwards [direction.continuous.continuousAt.eventually (dp.eventually (by decide))] with y hy
  have d := (hy.differentiableAt (by decide)).hasFDerivAt.comp y direction.hasFDerivAt
  unfold along
  rw [d.fderiv]
  exact (fderiv ℝ h (direction y)).map_zero

/-- Actual geodesic entrance data on a compact set produce a strictly positive Levi
collar. The angular weight is constructed from the scalar Jacobi equation. -/
theorem exists_collar_of_entrance {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ G] {S : Set Direction} (hS : IsCompact S)
    {σ : ℂ → ℝ} (simple : SimpleDiskTarget.SimpleMetric σ)
    {T : ℝ} (hT : 0 ≤ T) (entry : Direction → G) (τ : Direction → ℝ)
    (φ : Direction → ℝ → Direction) (z : G → ℝ → ℂ) (θ : G → ℝ → ℝ)
    (he : ∀ p ∈ S, ContDiffAt ℝ ∞ entry p) (hτ : ∀ p ∈ S, ContDiffAt ℝ ∞ τ p)
    (ht : ∀ p ∈ S, τ p ∈ Ioo 0 T) (base : ∀ p ∈ S, z (entry p) (τ p) = p.1)
    (hz : ∀ p ∈ S, ContDiffOn ℝ ∞ (z (entry p)) (Icc 0 T))
    (hg : ∀ p ∈ S, SimpleDiskTarget.unitGeodesicOn σ (z (entry p)) (θ (entry p)) (Icc 0 (τ p)))
    (hdisk : ∀ p ∈ S, ∀ t ∈ Icc 0 (τ p), z (entry p) t ∈ Metric.closedBall 0 1)
    (hzero : ∀ p ∈ S, φ p 0 = p)
    (hflow : ∀ p ∈ S, ∀ᶠ s in 𝓝 (0 : ℝ), HasDerivAt (φ p) (project (X σ) (φ p s)) s ∧
      entry (φ p s) = entry p ∧ τ (φ p s) = τ p + s) :
    ∃ h : Direction → ℝ, (∀ p ∈ S, ContDiffAt ℝ ∞ h p) ∧ ∃ η > 0,
      ∀ p : Chart, direction p ∈ S → p.2.2 < 0 → t p < η → ∀ w : Chart, w ≠ 0 →
        0 < ddC (J σ) (potential (frame σ) (h ∘ direction)) p w (J σ p w) := by
  have hk : ContinuousOn (fun p => SimpleDiskTarget.curvature σ (z (entry p) (τ p))) S :=
    (continuous_jet simple.smooth (h := fun _ => 0) (S := S) (fun _ _ => contDiffAt_const)).curvature.congr (fun p hp => congrArg (SimpleDiskTarget.curvature σ) (base p hp))
  have dx := (project_smooth (smooth_XH simple.smooth).1).differentiable (by simp)
  obtain ⟨h,hh⟩ := SmoothJacobiFamily.exists_smooth_angular_weight hS simple hT entry τ
    (project (X σ)) φ z θ he hτ ht hk hz hg hdisk (fun p _ => dx p) hzero hflow
  refine ⟨h,fun p hp => (hh p hp).1,uniform_collar simple.smooth hS (fun p hp => (hh p hp).1.of_le (by decide)) ?_⟩
  intro p hp
  simpa only [along, base p hp] using (hh p hp).2

end TransportOkaGrauert.PolarCollar
