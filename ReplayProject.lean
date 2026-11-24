import LeanChecker

/-! Invoke the pinned Lean toolchain's own leanchecker routine on every project
module, sequentially to keep peak memory bounded. Each module is replayed
against its imported environment. Lean and mathlib are the trusted upstream
dependencies. The umbrella is replayed last. -/
open Lean in
private unsafe def replayProject : IO Unit := do
  let dir : System.FilePath := "TransportOkaGrauert"
  let entries ← dir.readDir
  let modules := entries.filterMap fun e =>
    if e.path.extension = some "lean" then e.path.fileStem else none
  if modules.isEmpty then throw <| IO.userError "No Lean source modules found"
  let mut checked := 0
  for name in modules.qsort (· < ·) do
    replayFromImports (`TransportOkaGrauert ++ name.toName)
    checked := checked + 1
    if checked % 25 == 0 then
      IO.println s!"Kernel replayed {checked} of {modules.size} project modules."
      (← IO.getStdout).flush
  replayFromImports `TransportOkaGrauert
  IO.println s!"Replayed {modules.size} project modules and the library umbrella through Lean's kernel."

#eval replayProject
