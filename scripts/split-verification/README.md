# Split verification tooling

The scripts that produced the evidence in the top-level README's "Verification of the
split" section. They are Lean `--run` scripts and small Python comparators; none of them
is part of the library build.

| File | Purpose |
|---|---|
| `01-deps-dump.lean` | Dump every constant of the `Solution` module with its in-module `usedConstants` edges (`.deps-dump.txt`). Run against the ORIGINAL single-file build; this is the true dependency graph the partition was computed from. |
| `02-names-after.lean` | Dump the constant names of the split build (`Solution` + every `HopfProblem.*` module). |
| `03-type-hashes.lean` | Dump `name ⟶ Expr.hash (type)` for every project constant. |
| `04-type-hashes-demangled.lean` | Same, after rewriting every `_private.<module>.0.<n>` constant reference inside the type to `<n>`, so a private lemma's new module does not perturb the hash. |
| `05-pretty-print-types.lean` | Pretty-print the statements of a given list of constants (used to inspect the residual hash differences). |
| `verify-names.py` | Compare the constant-name sets before/after modulo private mangling and compiler auxiliaries. |
| `verify-types.py` | Compare the type hashes before/after; report missing/extra/changed. |

Recipe: `lake env lean --run scripts/split-verification/<script>.lean [args]` in each tree
(original file in a scratch worktree at the pre-split commit; split tree at HEAD), then the
two Python comparators with the dump paths edited at their top. The partition itself
(index extraction with Unicode-aware identifiers, folding of environment constants onto
source declarations, theme assignment, the greedy acyclic scheduler with private-lemma
co-location, the merge pass, and the emitter with attribute-block attachment) is
`partition.py` in this directory.
