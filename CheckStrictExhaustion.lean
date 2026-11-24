import TransportOkaGrauert.PhysicalSteinStrict
import Lean.Util.CollectAxioms

/-! Independent full-disk test. It spells out the sublevels and physical
Levi form, then audits the theorem's transitive axioms. The subsequent
universal Stein test separately requires the global holomorphic conclusions. -/
open TransportOkaGrauert ChartStein FrameLevi
open scoped ContDiff

example (σ : ℂ → ℝ) (s : SimpleDiskTarget.SimpleMetric σ) :
    ∃ f : E → ℝ, (∀ p ∈ ChartSteinAtlas.domain (Metric.ball (0:ℂ) 1),
      ContDiffAt ℝ ∞ f p ∧ ∀ v : E, v ≠ 0 →
        0 < ddC (PhysicalStein.J σ) f p v (PhysicalStein.J σ p v)) ∧
      ∀ m : ℝ, IsCompact {p ∈ ChartSteinAtlas.domain (Metric.ball (0:ℂ) 1) | f p ≤ m} :=
  PhysicalStein.full_disk_levi_exhaustion s

open Lean Elab Command in
run_cmd do
  let name := ``TransportOkaGrauert.PhysicalStein.full_disk_levi_exhaustion
  let env ← getEnv
  let (_, state) := ((CollectAxioms.collect name).run env).run {}
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let extra := state.axioms.filter (!allowed.contains ·)
  unless extra.isEmpty do throwError "Unapproved axioms in {name}: {extra}"
  logInfo m!"Full-disk strict exhaustion checked. Axiom dependencies: {state.axioms}"
