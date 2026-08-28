/- Dump the in-module constant dependency graph of Solution.olean.
   Run: lake env lean --run depdump.lean
   Output: .deps-dump.txt — first a numbered name table, then adjacency by index. -/
import Solution
import Lean
open Lean

def main : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{module := `Solution}] {} (trustLevel := 1)
  let some modIdx := env.getModuleIdx? `Solution
    | throw <| IO.userError "Solution module not found"
  let mut names : Array Name := #[]
  for (n, _) in env.constants.toList do
    if env.getModuleIdxFor? n == some modIdx then
      names := names.push n
  let idx : Std.HashMap Name Nat := names.foldl (init := {}) fun m n => m.insert n m.size
  let h ← IO.FS.Handle.mk ".deps-dump.txt" .write
  h.putStrLn s!"COUNT {names.size}"
  for n in names do
    h.putStrLn n.toString
  h.putStrLn "EDGES"
  for n in names do
    let some ci := env.find? n | continue
    let deps := ci.getUsedConstantsAsSet.toList.filterMap fun d => idx[d]?
    let some i := idx[n]? | continue
    h.putStrLn <| s!"{i}\t" ++ " ".intercalate (deps.map toString)
  h.flush
