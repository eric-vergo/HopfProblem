/-
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0

Authors: Eric Vergo, Claude Opus 5 (Claude Code)
-/
import Lean.Elab.Command
import HopfProblem

/-!
# Comparator sandbox regression fixture (CI only)

⚠️ **Do not open this file in an elaborating editor outside a sandbox, and do not
build the `SolutionProbe` library by hand.** Writing the canary files below is
its designed behaviour: outside the sandbox the writes succeed and it leaves
`comparator-probe-canary` in the working directory and in `$HOME`.

The repository-root `Solution.lean` with one addition: a top-level `run_cmd`
that tries to write files outside the comparator's Landlock sandbox, before any
declaration of this module is elaborated. Lean elaboration is arbitrary code
execution, so a comparator run that elaborates the solution *outside*
confinement lets that write succeed — the failure recorded as codex-audit
CX-012, where the workspace prebuilt `Challenge` and `Solution` and the
sandboxed `lake build` was left a no-op.

The fixture is driven by `comparator/config-probe.json` from the "Denied-write
probe" step of `.github/workflows/ci.yml`, and it is expected to FAIL:

* every write denied — the fixture aborts elaboration with the sentinel
  `COMPARATOR_PROBE_WRITES_DENIED`, the sandboxed `lake build` fails and the
  comparator exits non-zero. This is the passing outcome; CI matches the
  sentinel so that an unrelated failure cannot be mistaken for it.
* any write accepted — this module stays silent, `import HopfProblem` supplies
  `Mathoverflow1973.mathoverflow_1973` exactly as the real solution does, the
  comparator exits 0 and the canary files are on disk. CI fails on both signals.

Known limitation, and the reason this is no longer the primary evidence
(codex-audit CX-051): this file is a repository file, so a fixture edited to
throw the sentinel while attempting nothing would satisfy every acceptance
predicate. The containment evidence is the workflow's own "Trusted pre-run
sandbox self-test" step, whose bytes, write targets and sentinels are generated
per run outside the checkout and whose outcome is classified from the
filesystem. This fixture is kept as defense in depth: it still exercises the
comparator's own driver against the real solution's imports, and it still fails
closed.

It is registered as the `SolutionProbe` lake lib but is deliberately not a
default target and nothing imports it.
-/

namespace SolutionProbe

/-- The paths the probe writes to. Both parent directories always exist, so a
refused write is a denial rather than a missing directory: the process working
directory, which is inside the repository checkout the sandbox mounts read-only
(next to the comparator config, `Challenge.lean` and `Solution.lean`), and the
home directory, outside the checkout, where the landrun and nanoda binaries
live. -/
private def probeTargets : IO (Array String) := do
  let cwd ← IO.currentDir
  let mut targets : Array String := #[cwd.toString ++ "/comparator-probe-canary"]
  if let some home := (← IO.getEnv "HOME") then
    targets := targets.push (home ++ "/comparator-probe-canary")
  return targets

/-- Attempt one write, reporting whether it was accepted. -/
private def tryWrite (target : String) : IO Bool := do
  try
    IO.FS.writeFile (System.FilePath.mk target)
      "comparator sandbox breach: an elaboration-time write succeeded\n"
    return true
  catch _ =>
    return false

/-- The targets whose writes were accepted; empty means the sandbox held. -/
private def attemptEscape (targets : Array String) : IO (Array String) := do
  let mut written : Array String := #[]
  for target in targets do
    if (← tryWrite target) then
      written := written.push target
  return written

end SolutionProbe

run_cmd do
  let targets ← SolutionProbe.probeTargets
  let written ← SolutionProbe.attemptEscape targets
  if written.isEmpty then
    let names := String.intercalate ", " targets.toList
    throwError "COMPARATOR_PROBE_WRITES_DENIED: every elaboration-time write outside the sandbox was refused (tried: {names})"
