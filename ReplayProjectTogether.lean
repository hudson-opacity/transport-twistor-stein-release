import LeanChecker

/-! Kernel replay with a shared dependency environment. Read the private
constant table of every local module. The base environment contains
exclusively upstream modules. Lean's own verifier checks the entire local
table in dependency order and regenerates the recursors and constructors. -/
open Lean in
private unsafe def verifyProjectTogether : IO Unit := do
  let dir : System.FilePath := "TransportOkaGrauert"
  let entries ← dir.readDir
  let mut modules := (entries.filterMap fun e =>
    if e.path.extension = some "lean" then e.path.fileStem.map
      (fun stem => `TransportOkaGrauert ++ stem.toName) else none)
  if modules.isEmpty then throw <| IO.userError "No project sources found"
  modules := modules.push `TransportOkaGrauert
  let mut imports : Array Import := #[]
  let mut constants : Std.HashMap Name ConstantInfo := {}
  for modName in modules do
    let file ← findOLean modName
    let mut files := #[file]
    let server := OLeanLevel.server.adjustFileName file
    if ← server.pathExists then
      files := files.push server
      let privateFile := OLeanLevel.private.adjustFileName file
      if ← privateFile.pathExists then files := files.push privateFile
    let parts ← readModuleDataParts files
    let some first := parts[0]? | throw <| IO.userError s!"No data for {modName}"
    let some last := parts.back? | throw <| IO.userError s!"No private table for {modName}"
    for im in first.1.imports do
      unless Name.isPrefixOf `TransportOkaGrauert im.module || imports.contains im do
        imports := imports.push im
    let data := last.1
    for n in data.constNames, ci in data.constants do
      if let some old := constants[n]? then
        match old, ci with
        | .thmInfo a, .thmInfo b =>
          unless a.levelParams == b.levelParams && a.type == b.type && a.value == b.value && a.all == b.all do
            throw <| IO.userError s!"Different equation theorem at {n}"
        | _, _ => throw <| IO.userError s!"Duplicate non-theorem at {n}"
      else
        constants := constants.insert n ci
  let (_, state) ← importModulesCore imports |>.run
  let env ← finalizeImport state imports {} 0 false false (isModule := true)
  if env.header.moduleNames.any (Name.isPrefixOf `TransportOkaGrauert) then
    throw <| IO.userError "Project module present in the upstream base environment"
  unless constants.contains `TransportOkaGrauert.GeneralStein.universal_chart &&
      constants.contains `TransportOkaGrauert.GeneralStein.universal_manifold do
    throw <| IO.userError "Missing universal theorems"
  for (n, _) in constants do
    if (env.toKernelEnv.find? n).isSome then throw <| IO.userError s!"Upstream/project declaration overlap at {n}"
  IO.println s!"Replaying {constants.size} local declarations from {modules.size} modules against upstream dependencies only."
  (← IO.getStdout).flush
  let checked ← env.replay' constants
  let mut runtime := #[]
  for (n,ci) in constants do
    if ci.isUnsafe || ci.isPartial then
      runtime := runtime.push n
    else
      unless (checked.toKernelEnv.find? n).isSome do
        throw <| IO.userError s!"Declaration absent from the rebuilt kernel environment: {n}"
  unless (checked.toKernelEnv.find? `TransportOkaGrauert.GeneralStein.universal_chart).isSome &&
      (checked.toKernelEnv.find? `TransportOkaGrauert.GeneralStein.universal_manifold).isSome do
    throw <| IO.userError "Missing Stein conclusion after kernel reconstruction"
  IO.println s!"Kernel accepted {constants.size-runtime.size} logical declarations, including both universal Stein theorems."
  IO.println s!"The compiler's separate runtime declarations omitted by LeanChecker: {runtime}"
  checked.freeRegions

#eval verifyProjectTogether
