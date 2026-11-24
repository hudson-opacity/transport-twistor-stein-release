import TransportOkaGrauert
import TransportOkaGrauert.ChartStein
import TransportOkaGrauert.FlatStein
import TransportOkaGrauert.GeneralSteinReduction
import Lean.Util.CollectAxioms

/-! An acceptance test for the universal chart theorem. A successful build of
the library is a separate check. The theorem name is unrestricted within the
project namespace. Ordinary parameters, extra hypotheses, and a declaration
whose value merely defines the target proposition do not satisfy this test. -/
open Lean Meta Elab Command

-- Keep the quantifiers and the conclusion visible even if the target is edited.
example : TransportOkaGrauert.ChartStein.GeneralSimpleSurfaceStatement ↔
    (∀ σ : ℂ → ℝ, TransportOkaGrauert.SimpleDiskTarget.SimpleMetric σ →
      ∀ U : Set ℂ, IsOpen U → U ⊆ Metric.ball 0 1 →
        TransportOkaGrauert.ChartStein.HasSteinProperties σ U) := Iff.rfl

-- Check the precise current reduction before testing for a premise-free proof.
example : TransportOkaGrauert.SteinMomentBridge.InteriorMeanStatement →
    TransportOkaGrauert.ChartStein.GeneralSimpleSurfaceStatement ∧
      TransportOkaGrauert.ManifoldStein.GeneralManifoldStatement :=
  TransportOkaGrauert.SteinMomentBridge.universal_of_interior_mean

-- The hypotheses of the target have a concrete inhabited example.
example : TransportOkaGrauert.SimpleDiskTarget.SimpleMetric (fun _ => 0) :=
  TransportOkaGrauert.FlatSimple.euclidean_simple

private def projectProofsOf (target : Expr) : MetaM (Array Name) := do
  let env ← getEnv
  let mut hits := #[]
  for (n, ci) in env.constants.toList do
    if `TransportOkaGrauert |>.isPrefixOf n then
      if let .thmInfo _ := ci then
        let type := ci.type
        if ← withNewMCtxDepth <| withTransparency .all <| isDefEq type target then
          hits := hits.push n
  return hits

set_option maxHeartbeats 12000000 in
run_cmd do
  let flat := ``TransportOkaGrauert.FlatStein.constant_conformal_factor
  let flatHits ← liftTermElabM <| projectProofsOf (← getConstInfo flat).type
  unless flatHits.contains flat do throwError "Detector failed the proved flat control"
  let curved := ``TransportOkaGrauert.ManifoldStein.poincare
  let curvedHits ← liftTermElabM <| projectProofsOf (← getConstInfo curved).type
  unless curvedHits.contains curved do throwError "Detector failed the proved nonflat manifold control"
  let statement := ``TransportOkaGrauert.ChartStein.GeneralSimpleSurfaceStatement
  let manifold := ``TransportOkaGrauert.ManifoldStein.GeneralManifoldStatement
  let chartHits ← liftTermElabM <| projectProofsOf (mkConst statement)
  let manifoldHits ← liftTermElabM <| projectProofsOf (mkConst manifold)
  if chartHits.contains flat || manifoldHits.contains curved then
    throwError "A model-specific result was mistaken for a universal theorem"
  if chartHits.contains ``TransportOkaGrauert.GeneralSteinReduction.of_scalar_and_geometry ||
      manifoldHits.contains ``TransportOkaGrauert.ManifoldStein.manifold_of_chart then
    throwError "A conditional reduction was mistaken for a universal theorem"
  if chartHits.isEmpty || manifoldHits.isEmpty then
    throwError "Universal Stein proof incomplete. Exact chart theorems: {chartHits}. Exact manifold theorems: {manifoldHits}."
  let hits := chartHits ++ manifoldHits
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for n in hits do
    let (_, s) := ((CollectAxioms.collect n).run env).run {}
    let extra := s.axioms.filter (!allowed.contains ·)
    unless extra.isEmpty do throwError "Unapproved axioms in {n}: {extra}"
  logInfo m!"General Stein theorem checked: {hits}"
