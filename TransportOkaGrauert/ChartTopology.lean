import TransportOkaGrauert.ChartOrbits

/-!
# The smooth attenuation space on the disk chart

Use uniform convergence of every real derivative on the closed base disk
and one full angular period. Ambient representatives agreeing on the disk
have the same jets there, so this topology deliberately ignores differences
outside the physical base. Each attenuation is joined to zero by scalar
multiplication.
-/

noncomputable section
namespace TransportOkaGrauert.ChartTopology

open SimpleDiskTarget ChartOrbits Metric Real Set
open scoped ContDiff

/-- Smooth attenuations with the actual Fourier cutoff. -/
@[ext] structure Attenuation (n : ℕ) where
  val : Field n
  smooth : SmoothToBoundary val
  modes : ModesFrom (-1) val

variable {n : ℕ}
local instance : Fact (0 < 2 * π) := ⟨Real.two_pi_pos⟩

instance : Zero (Attenuation n) where
  zero := ⟨0, fun _ _ _ _ _ => contDiffAt_const, by
    intro z hz i j k hk
    simp [fourierCoeff]⟩

/-- The scalar ray stays in the attenuation space. -/
def scale (c : ℝ) (A : Attenuation n) : Attenuation n where
  val := c • A.val
  smooth := fun z hz θ i j => (A.smooth z hz θ i j).const_smul c
  modes := by
    intro z hz i j k hk
    change fourierCoeff (fun θ : DiskSeries.Angle => (c:ℂ) * A.val z θ.toCircle i j) k = 0
    rw [fourierCoeff.const_mul, A.modes z hz i j k hk, mul_zero]

private abbrev Cylinder := (closedBall (0 : ℂ) 1 ×ˢ Icc (-(π : ℝ)) π : Set (ℂ × ℝ))
private abbrev Jet (k : ℕ) := ContinuousMultilinearMap ℝ (fun _ : Fin k => ℂ × ℝ) ℂ

private instance : CompactSpace Cylinder :=
  isCompact_iff_compactSpace.mp ((isCompact_closedBall (0 : ℂ) 1).prod isCompact_Icc)

private def jets (A : Attenuation n) (k : ℕ) (i j : Fin n) : C(Cylinder, Jet k) where
  toFun p := iteratedFDeriv ℝ k (fun q : ℂ × ℝ => A.val q.1 (Circle.exp q.2) i j) p.val
  continuous_toFun := continuousOn_iff_continuous_restrict.mp fun p hp =>
    ((A.smooth p.1 hp.1 p.2 i j).continuousAt_iteratedFDeriv (by exact_mod_cast le_top)).continuousWithinAt

/-- The C∞ topology on the chart is pulled back from the product of spaces
of continuous k-th derivatives on the compact chart cylinder. -/
instance : TopologicalSpace (Attenuation n) := TopologicalSpace.induced jets inferInstance

private theorem jets_scale (c : ℝ) (A : Attenuation n) (k : ℕ) (i j : Fin n) :
    jets (scale c A) k i j = c • jets A k i j := by
  ext p d
  exact congrArg (fun op : Jet k => op d)
    (iteratedFDeriv_const_smul_apply' (a := c)
      ((A.smooth p.val.1 p.property.1 p.val.2 i j).of_le (by exact_mod_cast le_top)))

/-- Each scalar ray is continuous for uniform convergence of all derivatives. -/
theorem continuous_scale (A : Attenuation n) : Continuous (fun c : ℝ => scale c A) := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro k
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  change Continuous (fun c : ℝ => jets (scale c A) k i j)
  simp_rw [jets_scale]
  exact continuous_id.smul continuous_const

private theorem joined_zero (A : Attenuation n) : Joined (0 : Attenuation n) A := by
  refine ⟨⟨⟨fun t => scale (t : ℝ) A, (continuous_scale A).comp continuous_subtype_val⟩, ?_, ?_⟩⟩
  · apply Attenuation.ext
    change (0 : ℝ) • A.val = 0
    exact zero_smul _ _
  · apply Attenuation.ext
    exact one_smul ℝ A.val

instance : PathConnectedSpace (Attenuation n) :=
  ⟨⟨0⟩, fun a b => (joined_zero a).symm.trans (joined_zero b)⟩

/-- The published open-orbit argument on concrete chart attenuations. Its
analytic input is local relative frame existence in the smooth topology. -/
theorem frames_of_local (lam : ℂ → ℝ)
    (hloc : ∀ a : Attenuation n, ∃ V : Set (Attenuation n), IsOpen V ∧ a ∈ V ∧
      ∀ b ∈ V, ∃ F G, RelativeFrame lam a.val b.val F G) (A : Attenuation n) :
    ∃ F G, IsFrame lam A.val F G := by
  obtain ⟨F, G, h⟩ := relative_of_local lam Attenuation.val hloc A 0
  exact ⟨F, G, h.toFrame⟩

/-- The remaining local analytic theorem implies the complete open chart target. -/
theorem chartTarget_of_local
    (hloc : ∀ lam, SimpleMetric lam → ∀ n (a : Attenuation n),
      ∃ V : Set (Attenuation n), IsOpen V ∧ a ∈ V ∧
        ∀ b ∈ V, ∃ F G, RelativeFrame lam a.val b.val F G) : chartIntegratingFactorTarget := by
  intro lam hsimple n A hs hm
  exact frames_of_local lam (hloc lam hsimple n) ⟨A, hs, hm⟩

end TransportOkaGrauert.ChartTopology
