/- Pretty-print the statements of the given constants (names read from a file).
   Run: lake env lean --run depdump5.lean NAMES OUT -/
import Solution
import Lean
open Lean Meta

def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{module := `Solution}] {} (trustLevel := 1)
  let names := (← IO.FS.readFile args[0]!).splitOn "\n" |>.filter (· ≠ "")
  let h ← IO.FS.Handle.mk args[1]! .write
  for s in names do
    let n := s.toName
    match env.find? n with
    | none => h.putStrLn s!"### {s}\n<not found>"
    | some ci =>
      let (fmt, _) ← (ppExpr ci.type |>.run' {} {}).toIO { fileName := "", fileMap := default } { env := env }
      h.putStrLn s!"### {s}\n{fmt}\n"
  h.flush
