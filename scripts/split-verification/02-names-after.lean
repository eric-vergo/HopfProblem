/- Post-split verification: dump every project constant name (from Solution and
   all HopfProblem.* modules).  Run: lake env lean --run depdump2.lean -/
import Solution
import Lean
open Lean

def main : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{module := `Solution}] {} (trustLevel := 1)
  let h ← IO.FS.Handle.mk ".names-after.txt" .write
  for (n, _) in env.constants.toList do
    match env.getModuleIdxFor? n with
    | some idx =>
      let mod := env.header.moduleNames[idx.toNat]!
      if mod == `Solution || (`HopfProblem).isPrefixOf mod then
        h.putStrLn n.toString
    | none => pure ()
  h.flush
