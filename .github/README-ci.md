# CI topology

One workflow, `.github/workflows/ci.yml`, ported from
[`eric-vergo/OEIS-A362583-Irrationality`](https://github.com/eric-vergo/OEIS-A362583-Irrationality)
where it was built out over a long external audit (the `CX-0nn` references in the workflow
comments are that audit's finding numbers). Its purpose here is narrow and stated plainly:
**the comparator verdict this repository publishes is produced by a sandboxed GitHub Actions
run, not by anyone's laptop.**

## The trust boundary

Lean elaboration is arbitrary code execution. The comparator's whole guarantee therefore
depends on *when* and *where* `Challenge` and `Solution` are first elaborated, so the
workflow is split into three jobs along that boundary rather than written as one.

| Job | Trust | Token | What it does |
|-----|-------|-------|--------------|
| `build` | trusted | `contents: read` | Pin assertions, `formalization.yaml` schema validation, the validator's own forged-record test suite, `lake build HopfProblem`, the axiom audit of `Mathoverflow1973.mathoverflow_1973`. Uploads the subject oleans. |
| `comparator` | **untrusted** | `contents: read`, no OIDC | Builds landrun + nanoda, self-tests the sandbox, proves containment with a workflow-owned probe, then runs `leanprover/comparator` — the first elaboration of `Challenge` and `Solution` anywhere in the pipeline, inside landrun. Emits `comparator-result.json`. |
| `publish` | trusted | `contents: write` | Re-validates that record field by field against its own trusted inputs, writes `comparator/comparator-status.json` and checks `site/trust/kernel-identities.json`, commits both back to `master` on push events. |

`build` deliberately builds only the `HopfProblem` library. The package's `defaultTargets`
are `Challenge` and `Solution`; a plain `lake build` would elaborate both in the job that
precedes the sandbox, which is the exact failure the split exists to prevent.

## What each guard is for

* **AF_UNIX guard.** The pinned comparator documents its guarantee under
  `systemd-run -p RestrictAddressFamilies=~AF_UNIX`, which closes a known landrun escape.
  The first step of the `comparator` job proves that wrapper is available and **fails
  closed** if it is not; nothing untrusted is elaborated without it, and the guard's state
  is recorded in the result record and required by the publish validator.
* **Landlock self-test.** `landrun --best-effort` degrades silently to no sandbox on a
  kernel without Landlock. The self-test turns that into a hard failure with a positive and
  a negative control for both the filesystem and the network. The network control is a
  loopback listener started by the workflow, so the assertion depends on no DNS, no egress
  policy and no third-party endpoint.
* **Trusted pre-run sandbox self-test.** Containment is established *before* the
  repository's own Lean is elaborated, by a scratch Lake package this workflow writes
  outside the checkout, importing only core Lean, with write targets and sentinels
  randomised per run and the outcome classified from the filesystem. A probe that ran
  afterwards could not protect a boundary already crossed, and a probe that is itself a
  repository file is not independent evidence.
* **Denied-write probe.** `comparator/SolutionProbe.lean` driven by
  `comparator/config-probe.json`, kept as *defense in depth* only — it exercises the
  comparator's own driver against the real solution's imports, which the scratch package
  cannot. Its limitation is stated in its own module docstring.
* **Input-hash manifests.** One script, run immediately before and immediately after the
  certified run, over the comparator, lean4export, landrun and nanoda binaries and the
  three certified sources. Any difference means the machinery or the sources moved
  mid-flight, and the record is rejected.
* **Publish revalidation.** `scripts/validate_comparator_result.py` re-derives or compares
  every field the status file will publish against this job's own trusted context, and
  rejects unknown keys as firmly as missing ones. Its rejection behaviour is itself tested,
  in the `build` job, in seconds, against committed forged records
  (`scripts/tests/`).

## Verifier pins

`LANDRUN_REF`, `NANODA_REF`, `COMPARATOR_TOOL_SHA` and `LEAN4EXPORT_REF` are commit pins in
the workflow's `env` block. **Verifier currency is a standing invariant**: these must
postdate the newest Lean kernel fix relevant to the toolchain this project pins, and they
are re-pinned deliberately, never floated.

The comparator tool is *not* checked out here. It is a Lake dependency
(`require Comparator` in `lakefile.toml`), so it is built from this workspace with this
project's own toolchain — which is the property the audit asked for (the tool must run on
the Lean release whose kernel then replays the export) obtained by construction rather than
by overwriting a `lean-toolchain` file. The effective pin is the `rev` in the committed
`lake-manifest.json`, which the `build` job holds to `COMPARATOR_TOOL_SHA`, and the upstream
tag is separately required to still name that commit.

The Lean kernel doing the primary replay is the toolchain's own, so it is the same
implementation checking its own work. **nanoda is the independent check that matters** —
`enable_nanoda` is on in `comparator/config.json`, and the run records which nanoda binary
ran.

## Checker identity (`site/trust/kernel-identities.json`)

The status artifact records `kernel_identities`: the repository, revision and executable
digest of the nanoda binary that replayed the export. That record is written by the
producer, so on its own it establishes nothing. `site/trust/kernel-identities.json` is the
second source — a pin committed in this repository, transcribed from the workflow's own
`NANODA_REF` — and the blueprint site treats a recorded identity as authenticated only where
the two agree (`verso.blueprint.trust.expectedKernelIdentities`).

The publish job therefore **asserts** that pin against the run and fails on disagreement;
it writes the file only when it is absent, to bootstrap the first run, and says so in the
log. A pin regenerated from the run it is meant to authenticate would agree by construction
and check nothing.

The pin carries no `executable_sha256` on purpose (the schema makes it optional): nanoda is
`cargo build`-ed on the hosted runner, so its digest moves with the runner image's Rust
toolchain. Pinning a value neither the author nor the workflow can reproduce would either
red the build on unrelated image bumps or, if auto-refreshed, authenticate nothing. The
digest is still published as run evidence in `comparator/comparator-status.json`.

## Triggers

* `push` to `master` — the full three jobs, with commit-back.
* `push` to `split` — `build` and `comparator` only; `publish` is gated on the branch, so
  the upstream-PR branch can show a green sandboxed verdict without a write token ever
  being minted for it.
  **This half is inert until the workflow file is also present on `split`**: Actions runs
  the workflow from the branch that was pushed. The trigger is written now so the intended
  behaviour is already spelled out when that happens.
* `workflow_dispatch` — everything except the commit-back (which is gated on `push`). The
  refreshed status file is still uploaded as an artifact.

Pushes that only touch `comparator/comparator-status.json` or
`site/trust/kernel-identities.json` are ignored, so the publish job's own commit cannot
retrigger the workflow.

## Deliberately not run in CI

**The blueprint site under `site/` is not built, gated or deployed here.** Its
`lake build Contents` pass takes roughly three hours at this scale and its output is on the
order of 20,000 pages; that is not a hosted-runner workload, and it is generated and
published out of band.

Everything in the source workflow that exists to protect *site generation* consequently has
no counterpart here, and their absence is a consequence of that decision rather than an
oversight:

* the trust-provenance gate (`check_trust_provenance.py`) and its forged-record fixtures —
  they guard against a warm `site/.lake` replaying a stale evidence page;
* the source-link revision gate over `decl-registry.json`;
* the off-origin / no-CDN asset gates over the generated HTML;
* the deploy-predicate coupling test — there is no `deploy` job and no Pages artifact;
* the site-build toolchain setup — no job in this workflow runs `lake` after the
  `comparator` job. (If one is ever added, it needs its own Lean setup: a job split does not
  inherit one.)

Also absent by design: a362583's byte-identity assertion over duplicated definitions. There,
`Challenge.ϱ` and `A362583.ϱ` are *different constants* bridged by an `rfl` lemma, so nothing
compared the challenge's own definitions against the library's. Here `Challenge.lean` and
`HopfProblem` declare the *same* fully-qualified names, so the comparator's export
comparison walks the statement's transitive constant closure across both environments and
covers exactly that drift itself.
