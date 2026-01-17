#!/bin/bash
# Check that CHANGELOG.md changes are in separate commits
set -euo pipefail

# Get the base branch (usually main or master)
BASE_BRANCH="${1:-origin/main}"

echo "Checking changelog commits against $BASE_BRANCH..."

# Get commits that are ahead of base branch
commits=$(git log --format=%H "$BASE_BRANCH"..HEAD 2>/dev/null || echo "")

if [ -z "$commits" ]; then
    echo "No commits to check (or already on base branch)."
    exit 0
fi

error_found=0

for commit in $commits; do
    files=$(git diff-tree --no-commit-id --name-only -r "$commit")
    if echo "$files" | grep -q "^CHANGELOG.md$"; then
        file_count=$(echo "$files" | wc -l | tr -d ' ')
        if [ "$file_count" -gt 1 ]; then
            echo "Error: Commit $commit modifies CHANGELOG.md with other files:"
            echo "$files" | sed 's/^/  /'
            echo ""
            error_found=1
        fi
    fi
done

if [ "$error_found" -eq 1 ]; then
    echo "CHANGELOG.md changes must be in their own dedicated commits."
    echo "Please amend or split the commits to separate changelog updates."
    exit 1
fi

echo "All changelog commits are properly isolated."
exit 0
