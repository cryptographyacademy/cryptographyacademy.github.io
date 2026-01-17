#!/bin/bash
# Setup complete development environment
# This script runs all setup scripts in order
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

echo "========================================"
echo "Cryptography Academy - Full Setup"
echo "========================================"
echo ""

# Run individual setup scripts
"$SCRIPT_DIR/setup-lean.sh"
echo ""
"$SCRIPT_DIR/setup-web.sh"

echo ""
echo "========================================"
echo "Setup complete!"
echo "========================================"
echo ""
echo "Next steps:"
echo "  1. Start development server: make serve"
echo "  2. Open http://localhost:4321"
echo ""
echo "For editor setup, see: https://cryptography.academy/setup/"
