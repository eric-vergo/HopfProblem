#!/usr/bin/env bash
# Package a locally generated blueprint site for the Pages deploy workflow.
#
# The site under site/ is generated on a workstation (its registry pass is a
# multi-hour job at this scale -- see .github/README-ci.md, "Deliberately not run
# in CI"), and CI serves it: .github/workflows/site-deploy.yml downloads the
# tarball this script produces from a GitHub Release, authenticates it against
# site/trust/site-build.json (the pin this script writes) and against the
# checkout (scripts/check_site_release.py), and publishes it to GitHub Pages.
#
# This script refuses to package anything the deploy gate would refuse, so the
# refusal happens here, in seconds, instead of after a release was cut:
#
#   * the worktree must be clean, the site's own provenance record must not be
#     marked dirty (a site that describes no commit is not published), and the
#     revision it was generated from must be HEAD or an ancestor of HEAD -- the
#     registry's source links and the build stamp name that revision, and the CI
#     gate holds every trust input at HEAD to what that generation read;
#   * the tree must fit GitHub Pages: refused over 900 MB (the documented limit is
#     1 GB and deployments near it time out), with a per-component size report
#     (declaration pages, node pages, -verso-data, the rest) written next to the
#     tarball so the next generation's page cap can be set from numbers;
#   * the off-origin gates (scripts/site_offline_gates.sh) must pass;
#   * the freshly written pin, the tarball and the tree must pass
#     scripts/check_site_release.py exactly as CI will run it.
#
# In CI this is the whole packaging step of ci.yml's site-generate job; the next
# job cuts the release and commits the pin.
#
# Usage, from the repository root, after `cd site && lake build Contents &&
# rm -rf _out/site && lake env lean --run Main.lean --output _out/site`:
#
#   scripts/package_site.sh [output directory, default ./_site-release]
#
# It prints the three commands that publish the result: cut the release with the
# tarball as its asset, commit the pin, push master. The pin push is what
# triggers the deploy; the release has to exist first.
set -euo pipefail

root="$(git rev-parse --show-toplevel)"
cd "$root"
site_root="site/_out/site/html-multi"
pin="site/trust/site-build.json"
out="${1:-$root/_site-release}"

die() { echo "package_site: $*" >&2; exit 1; }

[ -d "$site_root" ] || die "$site_root does not exist -- generate the site first"
[ -f "$site_root/-verso-data/trust-provenance.json" ] || die "no trust-provenance.json under $site_root"

# The pin is the one file this script itself writes; a stale pin from an earlier
# packaging is not dirt. Anything else uncommitted is.
if [ -n "$(git status --porcelain --untracked-files=normal -- . ":!$pin")" ]; then
  git status --short -- . ":!$pin" >&2
  die "the worktree has uncommitted changes; commit or stash them, then regenerate if they touched the site"
fi

head="$(git rev-parse HEAD)"
read -r gen dirty < <(python3 - "$site_root/-verso-data/trust-provenance.json" <<'PY'
import json, sys
record = json.load(open(sys.argv[1], encoding="utf-8"))
build = record.get("buildRevision") or {}
print(build.get("commit", ""), "true" if build.get("dirty") else "false")
PY
)
[ "$dirty" = "false" ] || die "the site's provenance record is marked dirty -- regenerate from a clean worktree"
if [ "$gen" != "$head" ]; then
  git merge-base --is-ancestor "$gen" "$head" 2>/dev/null \
    || die "the site was generated at ${gen:-<none>}, which is not on the history of HEAD $head -- regenerate under HEAD"
  echo "package_site: the site was generated at ${gen:0:7}; HEAD is ${head:0:7} (the CI gate re-hashes every trust input at HEAD against that generation)"
fi

# --- Size: one repository, one GitHub Pages site -------------------------------
mkdir -p "$out"
python3 - "$site_root" "$out/size-report.txt" <<'PY'
import os, sys
root, report = sys.argv[1], sys.argv[2]
LIMIT = 900_000_000
def tree(path):
    files = total = 0
    for dirpath, _d, names in os.walk(path):
        for n in names:
            files += 1; total += os.path.getsize(os.path.join(dirpath, n))
    return files, total
rows = []
whole = tree(root)
for label, rel in (("declaration pages (decl/)", "decl"), ("node pages (node/)", "node"),
                   ("-verso-data (registry, manifests, assets)", "-verso-data"),
                   ("xref.json", "xref.json")):
    p = os.path.join(root, rel)
    rows.append((label,) + (tree(p) if os.path.isdir(p) else ((1, os.path.getsize(p)) if os.path.isfile(p) else (0, 0))))
rest = (whole[0] - sum(r[1] for r in rows), whole[1] - sum(r[2] for r in rows))
rows.append(("everything else (chapters, index, PM, trust pages)",) + rest)
lines = ["site size report", "  {:52s} {:>7s} {:>10s}".format("component", "files", "MB")]
for label, files, total in rows:
    lines.append("  {:52s} {:7d} {:10.1f}".format(label, files, total / 1e6))
lines.append("  {:52s} {:7d} {:10.1f}".format("TOTAL", whole[0], whole[1] / 1e6))
decl = rows[0]
if decl[1]:
    lines.append("  mean declaration page: {:.1f} KB; headroom to the 900 MB gate at that size: {:d} more page(s)".format(
        decl[2] / decl[1] / 1e3, max(0, int((LIMIT - whole[1]) / (decl[2] / decl[1])))))
text = "\n".join(lines)
print(text)
open(report, "w", encoding="utf-8").write(text + "\n")
if whole[1] > LIMIT:
    print("package_site: {} bytes exceeds the {} byte gate for one GitHub Pages site".format(whole[1], LIMIT))
    sys.exit(1)
PY

bash scripts/site_offline_gates.sh "$site_root"

short="${gen:0:7}"
tag="site-$(date -u +%Y%m%d)-$short"
asset="site-$short.tar.gz"
mkdir -p "$out"
tarball="$out/$asset"
rm -f "$tarball"
# Deterministic member order; the hash is what the pin vouches for.
( cd site/_out/site && find html-multi -type f | LC_ALL=C sort | tar -cf - -T - | gzip -n -6 > "$tarball" )

repository="$(git remote get-url origin | sed -E 's#^(https://github\.com/|git@github\.com:)##; s#\.git$##')"

python3 - "$pin" "$tarball" "$site_root" "$gen" "$tag" "$asset" <<'PY'
import datetime, hashlib, json, os, sys

pin, tarball, site_root, head, tag, asset = sys.argv[1:7]

digest = hashlib.sha256()
with open(tarball, "rb") as handle:
    for chunk in iter(lambda: handle.read(1 << 20), b""):
        digest.update(chunk)

files = sum(len(names) for _, _, names in os.walk(site_root))

with open("site/lake-manifest.json", encoding="utf-8") as handle:
    manifest = json.load(handle)
pins = {}
for package in manifest.get("packages", []):
    if package.get("name") in ("VersoBlueprint", "verso", "subverso", "mathlib"):
        pins[package["name"]] = package.get("rev")
with open("site/lean-toolchain", encoding="utf-8") as handle:
    pins["toolchain"] = handle.read().strip()

document = {
    "schemaVersion": 1,
    "generationRevision": head,
    "generatedAt": datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
    "release": {
        "tag": tag,
        "asset": asset,
        "sha256": digest.hexdigest(),
        "bytes": os.path.getsize(tarball),
        "files": files,
    },
    "pins": pins,
}
with open(pin, "w", encoding="utf-8") as handle:
    json.dump(document, handle, indent=2, sort_keys=True)
    handle.write("\n")
print("wrote {}: {} ({} bytes, {} files) generated at {}".format(pin, asset, document["release"]["bytes"], files, head[:7]))
PY

cp "$pin" "$out/site-build.json"
python3 scripts/check_site_release.py \
  --pin "$pin" --tarball "$tarball" --site-root "$site_root" \
  --repo-root "$root" --head "$head" --repository "$repository"

cat <<EOF

Packaged. To publish (in this order -- the pin push triggers the deploy, so the
release must exist first):

  gh release create "$tag" --target "$gen" "$tarball" "$out/site-build.json" --repo "$repository" \\
    --title "Site build $short" \\
    --notes "Blueprint site generated at $gen. Deployed by .github/workflows/site-deploy.yml after scripts/check_site_release.py authenticates it against site/trust/site-build.json and this checkout."
  git add "$pin" && git commit -m "site: publish the build generated at $short"
  git push origin master
EOF
