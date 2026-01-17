#!/bin/bash
# Setup web development environment
# This script installs Node.js dependencies for the Astro website
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(dirname "$SCRIPT_DIR")"

echo "=== Setting up web environment ==="

# Check Node.js version
if ! command -v node &> /dev/null; then
    echo "Error: Node.js is not installed"
    echo "Please install Node.js 24+ from https://nodejs.org/"
    exit 1
fi

NODE_VERSION=$(node --version | sed 's/v//' | cut -d. -f1)
if [ "$NODE_VERSION" -lt 20 ]; then
    echo "Error: Node.js version $NODE_VERSION is too old"
    echo "Please install Node.js 24+ (current: $(node --version))"
    exit 1
fi

echo "Node.js version: $(node --version)"
echo "npm version: $(npm --version)"

# Install dependencies
echo ""
echo "=== Installing npm dependencies ==="
cd "$PROJECT_ROOT/web"
npm install

# Verify installation
echo ""
echo "=== Verifying web setup ==="
npm run build

echo ""
echo "=== Web setup complete ==="
