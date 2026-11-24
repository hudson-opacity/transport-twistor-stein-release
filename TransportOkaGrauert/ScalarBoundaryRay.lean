import TransportOkaGrauert.ScalarRayPrimitive

/-! # Intrinsic boundary-to-boundary data for the scalar ray transform -/
noncomputable section
namespace TransportOkaGrauert.ScalarRayPrimitive
open JacobiEnlargement GeodesicFlowExtension SimpleDiskTarget
open Set Metric MeasureTheory Complex
open scoped ContDiff Topology Interval

/-- The input data consists of integrals over the in-disk unit-speed
geodesic segments with both endpoints on the unit circle. -/
def boundary_ray_zero (σ : ℂ → ℝ) (f : ℂ → ℝ) : Prop :=
  ∀ (a b : ℝ), a < b → ∀ z θ, unitGeodesicOn σ z θ (Icc a b) →
    (∀ t ∈ Icc a b, ‖z t‖ ≤ 1) → ‖z a‖ = 1 → ‖z b‖ = 1 →
    (∫ t in a..b, f (z t)) = 0

theorem extension_ray_zero {σ : ℂ → ℝ} (F : Flow σ) {f : ℂ → ℝ} (hf : Continuous f)
    (off : ∀ z, 1 < ‖z‖ → f z = 0) (null : boundary_ray_zero σ f)
    (p : State) (T : ℝ) (hT : 0 < T) (h0 : 1 < ‖p.1‖) (he : 1 < ‖F.base p T‖) :
    ray F f p T = 0 := by
  let z := F.base p
  let θ := F.angle p
  let n := fun t => ‖z t‖
  let S := Icc 0 T ∩ {t | n t ≤ 1}
  have cz : Continuous z := continuous_fst.comp (F.smooth.continuous.comp (continuous_const.prodMk continuous_id))
  have cn : Continuous n := cz.norm
  have ck : IsCompact S := isCompact_Icc.inter_right (isClosed_le cn continuous_const)
  have n0 : 1 < n 0 := by simpa [n,z,Flow.base,F.initial] using h0
  have off' : ∀ q : ℂ, 1 ≤ ‖q‖ → f q = 0 := by
    have e : EqOn f (fun _ => 0) (closedBall (0:ℂ) 1)ᶜ := fun q hq => off q (by simpa using hq)
    have c := e.closure hf continuous_const
    rw [closure_compl,interior_closedBall (0:ℂ) one_ne_zero] at c
    exact fun q hq => c (by simpa using hq)
  have zint {a b : ℝ} (hab : a ≤ b) (outside : ∀ t ∈ Icc a b, 1 ≤ n t) :
      (∫ t in a..b, f (z t)) = 0 := by
    calc
      _ = ∫ _t in a..b, (0:ℝ) := intervalIntegral.integral_congr fun t ht =>
        off' (z t) (outside t (uIcc_of_le hab ▸ ht))
      _ = 0 := intervalIntegral.integral_zero
  change (∫ t in 0..T, f (z t)) = 0
  by_cases h : S.Nonempty
  · let a := sInf S
    let b := sSup S
    have ha : a ∈ S := (ck.isLeast_sInf h).1
    have hb : b ∈ S := (ck.isGreatest_sSup h).1
    have minA := (ck.isLeast_sInf h).2
    have maxB := (ck.isGreatest_sSup h).2
    have hab : a ≤ b := minA hb
    have ha1 : n a = 1 := by
      obtain ⟨s,hs,es⟩ := intermediate_value_Icc' ha.1.1 cn.continuousOn ⟨ha.2,n0.le⟩
      have sa := minA (show s ∈ S from ⟨⟨hs.1,hs.2.trans ha.1.2⟩,es.le⟩)
      rwa [le_antisymm hs.2 sa] at es
    have hb1 : n b = 1 := by
      obtain ⟨s,hs,es⟩ := intermediate_value_Icc hb.1.2 cn.continuousOn ⟨hb.2,he.le⟩
      have sb := maxB (show s ∈ S from ⟨⟨hb.1.1.trans hs.1,hs.2⟩,es.le⟩)
      rwa [le_antisymm sb hs.1] at es
    have za := zint ha.1.1 (fun t ht => by
      by_contra! hn
      have at' := minA (show t ∈ S from ⟨⟨ht.1,ht.2.trans ha.1.2⟩,hn.le⟩)
      linarith [show n t = 1 from le_antisymm ht.2 at' ▸ ha1])
    have zb := zint hb.1.2 (fun t ht => by
      by_contra! hn
      have bt := maxB (show t ∈ S from ⟨⟨hb.1.1.trans ht.1,ht.2⟩,hn.le⟩)
      linarith [show n t = 1 from le_antisymm bt ht.1 ▸ hb1])
    have inside := GeodesicNonreturn.stays_in_disk (F.geo p (Icc a b)) ha.2 hb.2
      (fun q hq => F.convex q hq.le)
    have o : unitGeodesicOn σ z θ (Icc a b) := by
      intro t ht
      have e := F.germ (inside t ht)
      simpa only [z,θ,e.eq_of_nhds,Isothermal.angularDrift,e.fderiv_eq] using (F.geo p (Icc a b) t ht)
    have zm : (∫ t in a..b, f (z t)) = 0 := by
      rcases eq_or_lt_of_le hab with eq|lt
      · simp [eq]
      · exact null a b lt z θ o inside ha1 hb1
    have i (a b : ℝ) : IntervalIntegrable (fun t => f (z t)) volume a b := (hf.comp cz).intervalIntegrable _ _
    have s₁ := intervalIntegral.integral_add_adjacent_intervals (i 0 a) (i a b)
    have s₂ := intervalIntegral.integral_add_adjacent_intervals (i 0 b) (i b T)
    linarith
  · exact zint hT.le fun t ht => by by_contra! hn; exact h ⟨t,ht,hn.le⟩

end TransportOkaGrauert.ScalarRayPrimitive
