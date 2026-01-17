#!/bin/bash
# Setup Lean 4 development environment
# This script installs elan (Lean version manager) and downloads Mathlib cache
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(dirname "$SCRIPT_DIR")"

echo "=== Setting up Lean 4 ==="

# Check if elan is already installed
if command -v elan &> /dev/null; then
    echo "elan is already installed: $(elan --version)"
else
    echo "Installing elan (Lean version manager)..."
    curl https://elan.lean-lang.org/elan-init.sh -sSf | sh -s -- -y --default-toolchain none

    # Source elan environment
    if [ -f "$HOME/.elan/env" ]; then
        source "$HOME/.elan/env"
    fi
fi

# Verify elan is available
if ! command -v elan &> /dev/null; then
    echo "Error: elan not found in PATH"
    echo "Please restart your terminal or run: source ~/.elan/env"
    exit 1
fi

echo "elan version: $(elan --version)"

# Setup Lean project
echo ""
echo "=== Setting up Lean project ==="
cd "$PROJECT_ROOT/lean"

# Install toolchain specified in lean-toolchain
echo "Installing Lean toolchain..."
elan install

echo "Lean version: $(lean --version)"

# Download Mathlib cache
echo ""
echo "=== Downloading Mathlib cache ==="
echo "This may take a few minutes on first run..."
lake exe cache get || echo "Warning: cache get failed, will build from source"

# Build project to verify setup
echo ""
echo "=== Building Lean project ==="
lake build

echo ""
echo "=== Lean setup complete ==="
