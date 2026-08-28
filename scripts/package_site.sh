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
#   * the worktree must be clean and HEAD must be the revision the site's own
#     provenance record says it was generated from, and that record must not be
#     marked dirty -- a site that describes no commit is not published;
#   * the off-origin gates (scripts/site_offline_gates.sh) must pass;
#   * the freshly written pin, the tarball and the tree must pass
#     scripts/check_site_release.py exactly as CI will run it.
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
[ "$gen" = "$head" ] || die "the site was generated at ${gen:-<none>} but HEAD is $head -- regenerate under HEAD"
[ "$dirty" = "false" ] || die "the site's provenance record is marked dirty -- regenerate from a clean worktree"

bash scripts/site_offline_gates.sh "$site_root"

short="${head:0:7}"
tag="site-$(date -u +%Y%m%d)-$short"
asset="site-$short.tar.gz"
mkdir -p "$out"
tarball="$out/$asset"
rm -f "$tarball"
# Deterministic member order; the hash is what the pin vouches for.
( cd site/_out/site && find html-multi -type f | LC_ALL=C sort | tar -czf "$tarball" --no-recursion -T - )

repository="$(git remote get-url origin | sed -E 's#^(https://github\.com/|git@github\.com:)##; s#\.git$##')"

python3 - "$pin" "$tarball" "$site_root" "$head" "$tag" "$asset" <<'PY'
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

python3 scripts/check_site_release.py \
  --pin "$pin" --tarball "$tarball" --site-root "$site_root" \
  --repo-root "$root" --head "$head" --repository "$repository"

cat <<EOF

Packaged. To publish (in this order -- the pin push triggers the deploy, so the
release must exist first):

  gh release create "$tag" "$tarball" --repo "$repository" \\
    --title "Site build $short" \\
    --notes "Blueprint site generated at $head. Deployed by .github/workflows/site-deploy.yml after scripts/check_site_release.py authenticates it against site/trust/site-build.json and this checkout."
  git add "$pin" && git commit -m "site: publish the build generated at $short"
  git push origin master
EOF
