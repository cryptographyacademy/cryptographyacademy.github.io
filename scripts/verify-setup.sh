#!/bin/bash
# Verify development environment is correctly set up
# This script checks all required tools and project state
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(dirname "$SCRIPT_DIR")"

echo "=== Verifying development environment ==="
echo ""

ERRORS=0

# Check elan
echo -n "Checking elan... "
if command -v elan &> /dev/null; then
    echo "OK ($(elan --version | head -1))"
else
    echo "MISSING"
    ERRORS=$((ERRORS + 1))
fi

# Check lean
echo -n "Checking lean... "
if command -v lean &> /dev/null; then
    echo "OK ($(lean --version | head -1))"
else
    echo "MISSING"
    ERRORS=$((ERRORS + 1))
fi

# Check lake
echo -n "Checking lake... "
if command -v lake &> /dev/null; then
    echo "OK ($(lake --version | head -1))"
else
    echo "MISSING"
    ERRORS=$((ERRORS + 1))
fi

# Check node
echo -n "Checking node... "
if command -v node &> /dev/null; then
    NODE_VERSION=$(node --version | sed 's/v//' | cut -d. -f1)
    if [ "$NODE_VERSION" -ge 20 ]; then
        echo "OK ($(node --version))"
    else
        echo "TOO OLD ($(node --version), need 20+)"
        ERRORS=$((ERRORS + 1))
    fi
else
    echo "MISSING"
    ERRORS=$((ERRORS + 1))
fi

# Check npm
echo -n "Checking npm... "
if command -v npm &> /dev/null; then
    echo "OK ($(npm --version))"
else
    echo "MISSING"
    ERRORS=$((ERRORS + 1))
fi

echo ""

# Check Lean project
echo -n "Checking Lean project builds... "
if [ -d "$PROJECT_ROOT/lean" ]; then
    cd "$PROJECT_ROOT/lean"
    if lake build 2>/dev/null; then
        echo "OK"
    else
        echo "BUILD FAILED"
        ERRORS=$((ERRORS + 1))
    fi
else
    echo "MISSING (lean/ directory not found)"
    ERRORS=$((ERRORS + 1))
fi

# Check web project
echo -n "Checking web dependencies... "
if [ -d "$PROJECT_ROOT/web/node_modules" ]; then
    echo "OK"
else
    echo "MISSING (run npm install in web/)"
    ERRORS=$((ERRORS + 1))
fi

echo -n "Checking web project builds... "
if [ -d "$PROJECT_ROOT/web" ]; then
    cd "$PROJECT_ROOT/web"
    if npm run build 2>/dev/null; then
        echo "OK"
    else
        echo "BUILD FAILED"
        ERRORS=$((ERRORS + 1))
    fi
else
    echo "MISSING (web/ directory not found)"
    ERRORS=$((ERRORS + 1))
fi

echo ""
echo "========================================"

if [ "$ERRORS" -eq 0 ]; then
    echo "All checks passed!"
    exit 0
else
    echo "$ERRORS check(s) failed"
    echo "Run ./scripts/setup-all.sh to fix issues"
    exit 1
fi
