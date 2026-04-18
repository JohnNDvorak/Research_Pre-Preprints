#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SRC="$ROOT/skills/self-drive-research-loop"
CODEX_HOME_DIR="${CODEX_HOME:-$HOME/.codex}"
DEST_PARENT="$CODEX_HOME_DIR/skills"
DEST="$DEST_PARENT/self-drive-research-loop"
TMP="$DEST.tmp.$$"

if [[ ! -f "$SRC/SKILL.md" ]]; then
  echo "Could not find skill source at $SRC" >&2
  exit 1
fi

mkdir -p "$DEST_PARENT"
rm -rf "$TMP"
mkdir -p "$TMP"
cp -R "$SRC"/. "$TMP"/
rm -rf "$DEST"
mv "$TMP" "$DEST"

echo "Installed self-drive-research-loop skill to:"
echo "$DEST"
echo
echo 'Start a new Codex session and ask:'
echo 'Use $self-drive-research-loop to set up a research loop for this problem.'
