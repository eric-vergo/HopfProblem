/- Statement hashes modulo private-name mangling: every `.const` whose name is
   `_private.<module>.0.<n>` is rewritten to `<n>` before hashing.
   Run: lake env lean --run depdump4.lean OUT -/
import Solution
import Lean
open Lean

def demangle (n : Name) : Name :=
  let s := n.toString
  if s.startsWith "_private." then
    match s.splitOn ".0." with
    | _ :: rest => Name.mkSimple ("PRIV." ++ ".0.".intercalate rest)
    | [] => n
  else n

def normExpr (e : Expr) : Expr :=
  e.replace fun
    | .const n ls => some (.const (demangle n) ls)
    | _ => none

def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{module := `Solution}] {} (trustLevel := 1)
  let h ← IO.FS.Handle.mk (args.headD ".types-norm.txt") .write
  for (n, ci) in env.constants.toList do
    match env.getModuleIdxFor? n with
    | some idx =>
      let mod := env.header.moduleNames[idx.toNat]!
      if mod == `Solution || (`HopfProblem).isPrefixOf mod then
        h.putStrLn s!"{demangle n}\t{(normExpr ci.type).hash}\t{ci.levelParams.length}"
    | none => pure ()
  h.flush
