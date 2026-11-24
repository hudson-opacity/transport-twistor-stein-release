import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-! # Smooth ambient restrictions in the real disk Hilbert space -/

noncomputable section
namespace TransportOkaGrauert.ScalarDiskHilbert

open MeasureTheory Metric Set Filter
open scoped ContDiff ENNReal Topology

abbrev μ : Measure ℂ := volume.restrict (ball 0 1)
abbrev H := Lp ℝ 2 μ

instance : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne

theorem ae_mem_disk : ∀ᵐ x ∂μ, x ∈ ball (0 : ℂ) 1 := ae_restrict_mem measurableSet_ball

theorem memLp_continuous (f : ℂ → ℝ) (hf : Continuous f) : MemLp f 2 μ := by
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn hf.continuousOn
  exact .of_bound hf.aestronglyMeasurable C (ae_mem_disk.mono fun x hx => hC x (ball_subset_closedBall hx))

def ofSmooth (f : ℂ → ℝ) (hf : ContDiff ℝ ∞ f) : H := (memLp_continuous f hf.continuous).toLp f

theorem ofSmooth_coeFn (f : ℂ → ℝ) (hf : ContDiff ℝ ∞ f) : (ofSmooth f hf : ℂ → ℝ) =ᵐ[μ] f :=
  MemLp.coeFn_toLp _

def smooth : Submodule ℝ H where
  carrier := {x | ∃ (f : ℂ → ℝ) (hf : ContDiff ℝ ∞ f), ofSmooth f hf = x}
  zero_mem' := by
    refine ⟨fun _ => 0,contDiff_const,Lp.ext ?_⟩
    exact (ofSmooth_coeFn _ _).trans (Lp.coeFn_zero ..).symm
  add_mem' := by
    rintro _ _ ⟨f,hf,rfl⟩ ⟨g,hg,rfl⟩
    refine ⟨fun x => f x + g x,hf.add hg,Lp.ext ?_⟩
    exact (ofSmooth_coeFn _ _).trans (((ofSmooth_coeFn f hf).add (ofSmooth_coeFn g hg)).symm.trans (Lp.coeFn_add _ _).symm)
  smul_mem' := by
    rintro c _ ⟨f,hf,rfl⟩
    refine ⟨fun x => c • f x,hf.const_smul c,Lp.ext ?_⟩
    exact (ofSmooth_coeFn _ _).trans (((ofSmooth_coeFn f hf).const_smul c).symm.trans (Lp.coeFn_smul _ _).symm)

theorem mem_smooth_iff (x : H) : x ∈ smooth ↔
    ∃ (f : ℂ → ℝ) (hf : ContDiff ℝ ∞ f), ofSmooth f hf = x := Iff.rfl

theorem smooth_dense : Dense (smooth : Set H) := by
  apply (Lp.dense_hasCompactSupport_contDiff (E := ℂ) (F := ℝ) (μ := μ) (p := 2) (by norm_num)).mono
  rintro x ⟨f,hx,_,hf⟩
  exact ⟨f,hf,Lp.ext ((ofSmooth_coeFn f hf).trans hx.symm)⟩

end TransportOkaGrauert.ScalarDiskHilbert
