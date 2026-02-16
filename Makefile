# Cryptography Academy - Makefile
#
# Standard targets for building, testing, and deploying the project.

SHELL := /bin/bash

# GNU sed detection for macOS compatibility
UNAME_S := $(shell uname -s)
ifeq ($(UNAME_S),Darwin)
    SED := $(shell command -v gsed 2>/dev/null)
    ifeq ($(SED),)
        $(warning GNU sed (gsed) not found on macOS. Install with: brew install gnu-sed)
        SED := sed
    endif
else
    SED := sed
endif

.PHONY: help
help: ## Show this help
	@grep -E '^[a-zA-Z0-9_-]+:.*?## .*$$' $(MAKEFILE_LIST) | sort | \
		awk 'BEGIN {FS = ":.*?## "}; \
		{printf "\033[36m%-30s\033[0m %s\n", $$1, $$2}'

# =============================================================================
# Setup
# =============================================================================

.PHONY: setup
setup: setup-lean setup-web ## Setup all development dependencies

.PHONY: setup-lean
setup-lean: ## Setup Lean 4 development environment
	@echo "Setting up Lean 4..."
	@if ! command -v elan &> /dev/null; then \
		echo "Installing elan..."; \
		curl https://elan.lean-lang.org/elan-init.sh -sSf | sh -s -- -y; \
	fi
	@source ~/.elan/env && cd lean && lake update

.PHONY: setup-web
setup-web: ## Setup web development environment
	@echo "Setting up web dependencies..."
	@cd web && npm install

# =============================================================================
# Build
# =============================================================================

.PHONY: build
build: build-lean build-web ## Build everything

.PHONY: build-lean
build-lean: ## Build Lean project
	@echo "Building Lean..."
	@source ~/.elan/env && lake build --dir=lean

.PHONY: build-web
build-web: ## Build website
	@echo "Building website..."
	@cd web && npm run build

.PHONY: build-web-verbose
build-web-verbose: ## Build website
	@echo "Building website..."
	@cd web && npm run build-verbose

# =============================================================================
# Development
# =============================================================================

.PHONY: serve
serve: ## Start development server
	@cd web && npm run dev

.PHONY: serve-lean
serve-lean: ## Start Lean language server
	@source ~/.elan/env && cd lean && lake serve

# =============================================================================
# Lint and Format
# =============================================================================

.PHONY: lint
lint: lint-lean lint-web lint-python ## Run all linters

.PHONY: lint-lean
lint-lean: ## Lint Lean code
	@echo "Linting Lean..."
	@source ~/.elan/env && cd lean && lake build

.PHONY: lint-web
lint-web: ## Lint web code
	@echo "Linting web..."
	@cd web && npm run lint 2>/dev/null || true

.PHONY: lint-python
lint-python: ## Lint Python code with ruff
	@echo "Linting Python..."
	@ruff check scripts/

.PHONY: format
format: format-lean format-web format-python fix-trailing-whitespace ## Format all code

.PHONY: format-lean
format-lean: ## Format Lean code (no-op, Lean doesn't have official formatter)
	@echo "Lean formatting: manual style adherence required"

.PHONY: format-web
format-web: ## Format web code
	@echo "Formatting web..."
	@cd web && npm run format 2>/dev/null || true

.PHONY: format-python
format-python: ## Format Python code with ruff
	@echo "Formatting Python..."
	@ruff format scripts/
	@ruff check --fix scripts/

.PHONY: check-format
check-format: check-trailing-whitespace ## Check code formatting
	@echo "Format check passed"

# =============================================================================
# Testing
# =============================================================================

.PHONY: test
test: test-lean test-web ## Run all tests

.PHONY: test-lean
test-lean: ## Test Lean proofs compile
	@echo "Testing Lean..."
	@source ~/.elan/env && lake build --dir=lean

.PHONY: test-web
test-web: ## Run web tests
	@echo "Testing web..."
	@cd web && npm test 2>/dev/null || true

# =============================================================================
# Check outdated dependencies
# =============================================================================

.PHONY: check-outdated
check-outdated: ## Check for outdated dependencies
	@echo "Checking npm dependencies..."
	@cd web && npm outdated 2>/dev/null || true
	@echo ""
	@echo "Checking Lean toolchain..."
	@source ~/.elan/env && elan show

# =============================================================================
# Clean
# =============================================================================

.PHONY: clean
clean: clean-lean clean-web ## Clean all build artifacts

.PHONY: clean-lean
clean-lean: ## Clean Lean build artifacts
	@echo "Cleaning Lean..."
	@source ~/.elan/env && lake clean --dir=lean 2>/dev/null || true

.PHONY: clean-web
clean-web: ## Clean web build artifacts
	@echo "Cleaning web..."
	@rm -rf web/dist web/node_modules/.cache

# =============================================================================
# Trailing whitespace
# =============================================================================

.PHONY: fix-trailing-whitespace
fix-trailing-whitespace: ## Remove trailing whitespaces from all files
	@echo "Removing trailing whitespaces..."
	@find . -type f \( \
		-name "*.lean" -o -name "*.toml" -o -name "*.md" -o -name "*.yaml" \
		-o -name "*.yml" -o -name "*.ts" -o -name "*.tsx" \
		-o -name "*.js" -o -name "*.jsx" -o -name "*.sh" \
		-o -name "*.json" -o -name "*.astro" -o -name "*.mdx" -o -name "*.css" \) \
		-not -path "./.git/*" \
		-not -path "./lean/.lake/*" \
		-not -path "./web/node_modules/*" \
		-not -path "./web/dist/*" \
		-exec $(SED) -i -e 's/[[:space:]]*$$//' {} \; 2>/dev/null || true
	@echo "Done."

.PHONY: check-trailing-whitespace
check-trailing-whitespace: ## Check for trailing whitespaces
	@echo "Checking for trailing whitespaces..."
	@files=$$(find . -type f \( \
		-name "*.lean" -o -name "*.toml" -o -name "*.md" -o -name "*.yaml" \
		-o -name "*.yml" -o -name "*.ts" -o -name "*.tsx" \
		-o -name "*.js" -o -name "*.jsx" -o -name "*.sh" \
		-o -name "*.json" -o -name "*.astro" -o -name "*.mdx" -o -name "*.css" \) \
		-not -path "./.git/*" \
		-not -path "./lean/.lake/*" \
		-not -path "./web/node_modules/*" \
		-not -path "./web/dist/*" \
		-exec grep -l '[[:space:]]$$' {} + 2>/dev/null || true); \
	if [ -n "$$files" ]; then \
		echo "Files with trailing whitespace:"; \
		echo "$$files" | sed 's/^/  /'; \
		exit 1; \
	else \
		echo "No trailing whitespace found."; \
	fi

# =============================================================================
# Data generation
# =============================================================================

METADATA_DIR ?= \
	$(HOME)/codes/dannywillems/poseidon-formalization/data/metadata

.PHONY: generate-papers-data
generate-papers-data: ## Generate papers.json from .astro files + metadata
	METADATA_DIR=$(METADATA_DIR) python3 scripts/generate_papers_data.py

# =============================================================================
# Deploy
# =============================================================================

.PHONY: deploy
deploy: build ## Build for production deployment
	@echo "Production build complete. Deploy web/dist/ to hosting."
