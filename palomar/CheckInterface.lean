module
public import Lean
public import Lean.Util.CollectAxioms

/-! Local 4.28 interface check. Load the statement and implementation in separate
environments, and compare the complete project-local statement dependency records.
The target theorem's proof is audited for transitive axioms in the Solution only. -/

open Lean

deriving instance BEq for QuotKind
deriving instance BEq for QuotVal
deriving instance BEq for InductiveVal
deriving instance BEq for ConstantInfo

private def checkInterface (challenge solution : Environment) : IO Unit := do
  let target := `SteinRegistry.stein_transport_twistor_interior
  let some (.thmInfo claim) := challenge.find? target | throw <| IO.userError "Challenge target missing"
  let some (.thmInfo proved) := solution.find? target | throw <| IO.userError "Solution target missing"
  unless claim.toConstantVal == proved.toConstantVal do
    throw <| IO.userError "The target theorem types differ"
  let mut pending := claim.type.getUsedConstants.toList
  let mut seen : NameSet := {}
  while !pending.isEmpty do
    let name := pending.head!
    pending := pending.tail!
    if seen.contains name then continue
    if !(`SteinRegistry).isPrefixOf name then continue
    let some left := challenge.find? name | throw <| IO.userError s!"Missing in Challenge: {name}"
    let some right := solution.find? name | throw <| IO.userError s!"Missing in Solution: {name}"
    unless left == right do throw <| IO.userError s!"Declaration differs: {name}"
    seen := seen.insert name
    pending := left.getUsedConstantsAsSet.toList ++ pending
  unless seen.contains `SteinRegistry.SimpleDiskTarget.SimpleMetricGerm.mk &&
      seen.contains `SteinRegistry.ChartStein.HasSteinProperties.mk &&
      seen.contains `SteinRegistry.ChartStein.SatisfiesCR do
    throw <| IO.userError "Geometric hypotheses, CR equations or Stein conclusions absent"
  if solution.header.moduleNames.contains `Challenge then
    throw <| IO.userError "Solution depends on Challenge"
  let (_, state) := ((CollectAxioms.collect target).run solution).run {}
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  unless state.axioms.all allowed.contains do throw <| IO.userError s!"Unexpected axioms: {state.axioms}"
  IO.println s!"Identical theorem signature and {seen.toList.length} project-local declarations in the statement closure, including definitions and constructor types."
  IO.println s!"Solution transitive axioms: {state.axioms}"

public unsafe def main : IO Unit := do
  initSearchPath (← findSysroot)
  withImportModules #[{module := `Challenge}] {} fun challenge =>
    withImportModules #[{module := `Solution}] {} (checkInterface challenge)
