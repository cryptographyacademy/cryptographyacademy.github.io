#!/usr/bin/env bash
# Verify that papers-history.json is updated when paper pages change.
#
# If any web/src/pages/papers/*.astro file (except index.astro) was
# added or modified in the PR, papers-history.json must also be
# modified in the same PR.
#
# Usage: check-papers-history.sh <base-sha>
set -euo pipefail

base="${1:?Usage: check-papers-history.sh <base-sha>}"

changed_papers=$(
    git diff --name-only --diff-filter=AM "${base}...HEAD" -- \
        'web/src/pages/papers/*.astro' \
    | grep -v 'index\.astro$' || true
)

if [ -z "$changed_papers" ]; then
    echo "No paper pages added or modified. Nothing to check."
    exit 0
fi

count=$(echo "$changed_papers" | wc -l | tr -d ' ')
echo "Found $count added/modified paper page(s):"
echo "${changed_papers//$'\n'/$'\n'  }" | sed '1s/^/  /'

history_changed=$(
    git diff --name-only "${base}...HEAD" -- \
        'web/src/data/papers-history.json' || true
)

if [ -z "$history_changed" ]; then
    echo ""
    echo "::error::papers-history.json was not updated."
    echo "Run 'make generate-papers-history' and commit the result."
    exit 1
fi

echo ""
echo "papers-history.json is updated. Check passed."
exit 0
