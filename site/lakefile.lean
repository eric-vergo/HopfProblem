/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Opus 5 (Claude Code)
-/
import Lake
open Lake DSL

-- Root-level git requires for the three Showcase forks, tracking their `blueprint`
-- branches.  The forks require each other from git too, so they build standalone;
-- requiring them HERE as well is what out-ranks verso-slides' transitive pin of the
-- upstream `leanprover/verso` (Lake resolves by NAME and honours the ROOT package's
-- `require`s first), keeping the site on the forks and preserving the offline /
-- self-hosted-`marked` invariant they provide.  The resolved commits are recorded in
-- lake-manifest.json; a `lake update subverso verso VersoBlueprint` re-pins to the
-- current `blueprint` HEAD of each fork.
--
-- Order matters: subverso, then verso (BEFORE anything that transitively pulls
-- verso-slides / upstream verso), then VersoBlueprint, then the subject, then
-- `mathlib` LAST — its post-update cache hook must run last (proofwidgets pin
-- tension: verso pins proofwidgets v0.0.104, mathlib carries its own rev).
require subverso from git "https://github.com/eric-vergo/subverso.git" @ "blueprint"
require verso from git "https://github.com/eric-vergo/verso.git" @ "blueprint"
require VersoBlueprint from git "https://github.com/eric-vergo/Showcase.git" @ "blueprint"
-- The subject formalization, as a PATH dependency on the repository root (the site is a
-- sub-package of the formalization repo, exactly as in the A362583 showcase).  This is
-- also what lets `workspaceModuleSourcePath?` find `../Solution.lean` for verbatim
-- signature/proof capture: the parent directory is scanned as a package root.
require HopfProblem from ".."
-- Mathlib at tag `v4.33.0` — the SAME tag the subject pins in its own lakefile.toml
-- (rev db584cd6d4).  Deliberately NOT the forks' v4.33.1: the site must elaborate the
-- subject's 385 MB `Solution.olean` from the shared repo-root `.lake/build`, and that
-- only happens when the toolchain and the Mathlib pin match the ones it was built with.
-- `site/lean-toolchain` is pinned to v4.33.0 for the same reason; do not "upgrade" it.
require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.33.0"

/-- URL of the CI run that produced these checks, read from the `CI_RUN_URL`
environment variable at configuration time.  Empty on a local build (the env var is
unset) ⇒ the comparator page renders no "View CI run" link, which is the expected local
behaviour.  A CI workflow sets `CI_RUN_URL` to a step-level deep link and passes
`-R`/`--reconfigure` on the `lake build Contents` step so this value is re-read fresh
each run — Lake's config trace keys off the lakefile *text* hash (plus
toolchain/platform), not env vars, so without `-R` a warm-cache run would splice in a
stale URL. -/
def ciRunUrl : String :=
  run_io return ((← IO.getEnv "CI_RUN_URL").getD "")

package Contents where
  precompileModules := false
  leanOptions := #[
    ⟨`experimental.module, true⟩,
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`maxSynthPendingDepth, .ofNat 3⟩,
    ⟨`weak.verso.blueprint.math.lint, true⟩,
    ⟨`weak.verso.blueprint.externalCode.strictResolve, true⟩,
    -- All-declarations registry + graph over the subject's ~20,600 declarations.
    -- NOTE on scale: the cap `graph.maxFlatVariantNodes` (1500) is on by default and
    -- this subject exceeds it by more than an order of magnitude.  That is INTENDED: the
    -- graph leads with Group View + per-parent drill-downs, and registry entries record
    -- the degraded (signature / syntactic) rendering tier rather than paying for full
    -- re-elaboration 20,600 times.
    ⟨`weak.verso.blueprint.graph.includeAllDecls, true⟩,
    -- Scale cap (f): full statement+proof re-elaboration from source, per declaration.
    -- The dominant time and memory cost of the Contents pass — 1500 (the default) is a
    -- ~3 h pass on a 24 GB workstation, which does not fit a hosted CI runner (4 vCPU,
    -- 16 GB, 6 h per job).  The site is built in CI (ci.yml `site-contents`), so this
    -- is set for that budget; the other ~20,000 declarations get a re-elaborated
    -- signature and a syntactically highlighted body, recorded per declaration as
    -- `sigTier` / `proofTier` in the registry.  Raise it once a CI run shows headroom.
    ⟨`weak.verso.blueprint.declRegistry.fullElabMaxDecls, .ofNat 300⟩,
    -- Which declarations get a PAGE, and what a page carries, is a stated policy sized
    -- for ONE GitHub Pages site (the documented limit is 1 GB; deployments near it time
    -- out; ci.yml's site-generate job refuses a tree over 900 MB and reports its size
    -- per component).  Every declaration stays in the registry, the index, the axiom
    -- audit and the dependency graph whatever the policy says about its page.
    --
    -- Policy (g): no page for INSTANCES and for PRIVATE declarations.  An instance is
    -- typeclass plumbing and a private declaration is an implementation detail of its
    -- module; both are indexed with their signature and a source link, neither is
    -- worth a page.  Counts are reported on the PM hub and the trust model.
    ⟨`weak.verso.blueprint.declRegistry.pageExcludeInstances, true⟩,
    ⟨`weak.verso.blueprint.declRegistry.pageExcludePrivate, true⟩,
    -- Scale cap (d): per-declaration PAGES, among the declarations policy (g) leaves,
    -- ranked by fan-in (the most-referenced first).  12000 is the first CI budget
    -- (≈ 30 KB per page after (e), (h), (i) below, plus ≈ 300 MB of registry, node pages
    -- and indexes); the size report of each run says how far it can be raised, and
    -- 0 means a page for every eligible declaration.
    ⟨`weak.verso.blueprint.declRegistry.maxDeclPages, .ofNat 12000⟩,
    -- Scale cap (e): the per-page LOCAL GRAPH, by node count.  The radius-2 neighborhood
    -- of a hub declaration in a 20,600-node graph is thousands of nodes — a multi-megabyte
    -- page nobody can read.  The page keeps the first 60 declarations met breadth-first
    -- and says how many within the radius it left out
    -- (`verso.blueprint.nodePage.localGraphMaxNodes`, Showcase 63dbb25).
    ⟨`weak.verso.blueprint.nodePage.localGraphMaxNodes, .ofNat 60⟩,
    -- Policy (h): a declaration page draws its local graph only when (e) did NOT truncate
    -- it.  A truncated hub graph is the largest payload on the site and an arbitrary
    -- breadth-first prefix of the real neighborhood; the rail's Uses / Used-by lists carry
    -- the whole of it.  Node pages (the 429 curated ones) keep their graphs.
    ⟨`weak.verso.blueprint.declPage.localGraphCompleteOnly, true⟩,
    -- Policy (i): no sidebar table of contents on declaration pages (they have the top
    -- navigation and a breadcrumb; the chapter ToC is ~5 KB repeated on every page).
    ⟨`weak.verso.blueprint.declPage.sidebarToc, false⟩,
    -- Automatic dependency inference: the subject carries no `@[blueprint]` edges, so
    -- graph provenance is machine-derived (CX-033) rather than author-declared.
    ⟨`weak.verso.blueprint.autoDeps, true⟩,
    -- Short-display the `Mathoverflow1973.` prefix everywhere (the subject is a single
    -- module in a single namespace); FQ names are preserved in titles and tooltips.
    ⟨`weak.verso.blueprint.declNamePrefix, "Mathoverflow1973"⟩,
    ⟨`weak.verso.blueprint.trust.formalizationYaml, "../formalization.yaml"⟩,
    -- Validate formalization.yaml against the v0.4 subset check on every build: a
    -- metadata page must not present a document this build could not read.
    ⟨`weak.verso.blueprint.trust.validateFormalizationYaml, true⟩,
    -- The comparator STATUS artifact: written by CI's publish job from the run's own
    -- evidence (first run 33136024687, 2026-08-28) and committed back to `master`.  This
    -- is one of the two options that HARD-ERROR when set to a path with no file at it
    -- (TrustStrip.lean `elabTrustData?`) — by design, so a configured signal cannot
    -- silently degrade into a probe.  Its `input_file` freshness edge is in `needs`.
    -- The Solution the comparator page embeds is the 62-line aggregator (the split
    -- module tree is presented through the registry), so verbatim embedding is cheap.
    ⟨`weak.verso.blueprint.trust.comparatorStatus, "../comparator/comparator-status.json"⟩,
    ⟨`weak.verso.blueprint.trust.requireAuditClean, true⟩,
    -- CX-064: named checker identity requires a consumer-controlled pin the run record must
    -- agree with.  `trust/kernel-identities.json` is written once by CI's publish job from the
    -- run's own nanoda build (bootstrap) and asserted on every later run; the site reads it at
    -- elaboration, so it also gets an `input_file` freshness edge below (CX-075).
    ⟨`weak.verso.blueprint.trust.expectedKernelIdentities, "trust/kernel-identities.json"⟩,
    ⟨`weak.verso.blueprint.trust.ciRunUrl, ciRunUrl⟩,
    -- The meaning closure of the certified claim (F1): what a reader must read to know
    -- what `Mathoverflow1973.mathoverflow_1973` SAYS.  Computed by the fork's
    -- `statement-closure` executable in a subprocess importing exactly the challenge
    -- chain's declared imports; labelled bound-to-the-verdict only when the chain it hashed
    -- matches the run record's `challenge_chain`.  Probe-and-degrade when the tool is absent.
    ⟨`weak.verso.blueprint.trust.statementClosure, true⟩,
    ⟨`weak.verso.code.warnLineLength, .ofNat 0⟩
  ]

-- The trust surfaces are captured at ELABORATION from the files the
-- `verso.blueprint.trust.*` options name, and none of them is a Lean module, so Lake
-- otherwise tracks no read of them: edit the config, the Challenge or the Solution,
-- rebuild, and a warm `.olean` republishes the entire prior evidence page — old verdict
-- beside the old statement, internally consistent — under the new build's revision
-- (codex-audit CX-075).  An `input_file` hashes each into the library's extra-dep job
-- trace, which Lake mixes into every module's `depTrace`, so an ordinary
-- `lake build Contents` re-elaborates the capture when one of them changes.
--
-- Three things here are load-bearing, per the recipe in the fork's
-- `VersoBlueprint.TrustFreshness` module docs:
--   * `needs`, never `extraDepTargets` — for a named-kind declaration (which
--     `input_file` is) Lake resolves `extraDepTargets` through a branch that neither
--     builds the target nor contributes a trace, i.e. a silent no-op;
--   * `path` is relative to the PACKAGE directory, so this sub-package site writes
--     `../…` exactly as the trust options above do;
--   * `text` stays at its default `false` — `text := true` normalizes line endings
--     before hashing, so a CRLF↔LF change would move the generator's byte digest
--     without moving Lake's trace, giving a build that fails the freshness gate and
--     cannot be fixed by rebuilding.
--
-- This is convenience, not the guarantee: `Informal.TrustFreshness` re-reads and
-- re-digests every recorded input before anything is written.  The edge is what keeps
-- that stop a backstop instead of the workflow.
--
-- `comparator/comparator-status.json` has no edge here because it has no file yet; add
-- one when the option above is enabled.
input_file formalizationYaml where
  path := "../formalization.yaml"

input_file comparatorConfig where
  path := "../comparator/config.json"

input_file comparatorChallenge where
  path := "../Challenge.lean"

input_file comparatorSolution where
  path := "../Solution.lean"

input_file kernelIdentities where
  path := "trust/kernel-identities.json"

input_file comparatorStatus where
  path := "../comparator/comparator-status.json"

@[default_target]
lean_lib Contents where
  needs := #[`@/formalizationYaml, `@/comparatorConfig,
             `@/comparatorChallenge, `@/comparatorSolution,
             `@/kernelIdentities, `@/comparatorStatus]
  roots := #[`Authors, `Contents, `Chapters, `Bibliography, `Macros]

@[default_target]
lean_exe «blueprint-gen» where
  root := `Main
  supportInterpreter := true
