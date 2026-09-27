#!/usr/bin/env bash
set -euo pipefail

root=$(git rev-parse --show-toplevel)
cd "$root"

command -v lake >/dev/null
command -v rg >/dev/null
command -v git >/dev/null

printf '%s\n' '== focused aggregate compile =='
lake env lean RayleighKernel.lean

printf '%s\n' '== lake build =='
lake build

printf '%s\n' '== production forbidden-token/settings scan =='
if rg -n -P '\b(?:sorry|admit)\b|sorryAx|^\s*axiom\b|native_decide|warningAsError\s+false|maxHeartbeats' \
    RayleighKernel --glob '*.lean'; then
  printf '%s\n' 'forbidden production token or setting found' >&2
  exit 1
fi
printf '%s\n' 'production scan passed (no matches)'

printf '%s\n' '== public axiom audit =='
lake env lean scripts/release-audit.lean

printf '%s\n' '== working-tree whitespace checks =='
git diff --check
git diff --cached --check

printf '%s\n' '== version consistency =='
lake_version=$(rg -N -o -r '$1' '^version = "(.+)"$' lakefile.toml)
cff_version=$(rg -N -o -r '$1' '^version: (\S+)$' CITATION.cff)
if [ "CITATION.cff:$cff_version" != "CITATION.cff:$lake_version" ]; then
  printf 'version mismatch: lakefile.toml=%s, CITATION.cff=%s\n' "$lake_version" "$cff_version" >&2
  exit 1
fi
major=${lake_version%%.*}
if ! rg -q "^\| $major\.x " SECURITY.md; then
  printf 'SECURITY.md does not declare %s.x as the supported line\n' "$major" >&2
  exit 1
fi
printf 'version %s consistent across lakefile.toml, CITATION.cff, SECURITY.md\n' \
  "$lake_version"

printf '%s\n' 'local release checks passed (no network operations performed)'
