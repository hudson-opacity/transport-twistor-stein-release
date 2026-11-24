import TransportOkaGrauert
import Lean.Util.CollectAxioms

/-! Find every loaded declaration originating in a project module, including private helpers and generated declarations, and traverse their proof dependencies. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let files ← System.FilePath.readDir "TransportOkaGrauert"
  for file in files do
    if file.path.extension = some "lean" then
      if let some stem := file.path.fileStem then
        let mod := `TransportOkaGrauert ++ stem.toName
        unless env.header.moduleNames.contains mod do
          throwError "Project module missing from the library umbrella: {mod}"
  let project := env.header.moduleNames.map (fun n => `TransportOkaGrauert |>.isPrefixOf n)
  let roots := env.constants.toList.filter fun (n, _) =>
    match env.getModuleIdxFor? n with
    | some idx => project[idx.toNat]!
    | none => false
  if roots.isEmpty then throwError "No project declarations found"
  let (_, state) := ((roots.forM (fun (n, _) => CollectAxioms.collect n)).run env).run {}
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let extra := state.axioms.filter (!allowed.contains ·)
  unless extra.isEmpty do throwError "Unexpected axiom dependencies: {extra}"
  logInfo m!"Checked {roots.length} project declarations. Axiom dependencies: {state.axioms}"
