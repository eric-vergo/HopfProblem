/- Dump statement-type hashes for every source-level project constant.
   Run: lake env lean --run depdump3.lean OUT -/
import Solution
import Lean
open Lean

def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{module := `Solution}] {} (trustLevel := 1)
  let h ← IO.FS.Handle.mk (args.headD ".types.txt") .write
  for (n, ci) in env.constants.toList do
    match env.getModuleIdxFor? n with
    | some idx =>
      let mod := env.header.moduleNames[idx.toNat]!
      if mod == `Solution || (`HopfProblem).isPrefixOf mod then
        h.putStrLn s!"{n}\t{ci.type.hash}\t{ci.levelParams.length}"
    | none => pure ()
  h.flush
