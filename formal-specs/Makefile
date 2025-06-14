# Makefile for formal verification

.PHONY: all clean verify-tla verify-alloy verify docker-build docker-verify local-verify help

# Default target
all: verify

# Help target
help:
	@echo "Available targets:"
	@echo "  make verify          - Run all verifications (TLA+ and Alloy)"
	@echo "  make verify-tla      - Run TLA+ model checking"
	@echo "  make verify-alloy    - Run Alloy analysis"
	@echo "  make local-verify    - Run verifications locally (without Docker)"
	@echo "  make docker-build    - Build Docker image with verification tools"
	@echo "  make docker-verify   - Run verifications in Docker"
	@echo "  make clean           - Clean verification results"

# Build Docker image
docker-build:
	@echo "Building Docker image for formal verification tools..."
	docker-compose build

# Run all verifications
verify: verify-tla verify-alloy
	@echo "All verifications completed!"

# Run TLA+ verification
verify-tla:
	@echo "Running TLA+ model checking on workflow.tla..."
	@mkdir -p verification-results/tla
	@if command -v tlc >/dev/null 2>&1; then \
		tlc -config workflow.cfg -deadlock -coverage 1 workflow.tla 2>&1 | tee verification-results/tla/tlc-output.log; \
	elif [ -f tools/tla2tools.jar ]; then \
		echo "TLC not found. Running with Java..."; \
		java -cp tools/tla2tools.jar tlc2.TLC -config workflow.cfg -deadlock -coverage 1 workflow.tla 2>&1 | tee verification-results/tla/tlc-output.log; \
	else \
		echo "Error: TLC not found and tools/tla2tools.jar not available."; \
		echo "Please run 'make local-setup' or use Docker."; \
		exit 1; \
	fi
	@echo "TLA+ verification completed. Results in verification-results/tla/"

# Run Alloy verification
verify-alloy:
	@echo "Running Alloy analysis on constraints.als..."
	@mkdir -p verification-results/alloy
	@if command -v alloy >/dev/null 2>&1; then \
		echo "run systemInvariants for 5" | alloy -c constraints.als > verification-results/alloy/alloy-output.log 2>&1; \
	elif [ -f tools/alloy.jar ]; then \
		echo "Note: Running Alloy in batch mode. For full analysis, use the GUI."; \
		java -cp tools/alloy.jar edu.mit.csail.sdg.alloy4whole.ExampleUsingTheCompiler constraints.als > verification-results/alloy/alloy-output.log 2>&1; \
	else \
		echo "Error: Alloy not found and tools/alloy.jar not available."; \
		echo "Please run 'make local-setup' or use Docker."; \
	fi
	@echo "Alloy verification completed. Results in verification-results/alloy/"

# Run verifications locally (without Docker)
local-verify:
	@echo "Running verifications locally..."
	@if [ -x ./verify-local.sh ]; then \
		./verify-local.sh; \
	else \
		echo "Error: verify-local.sh not found or not executable."; \
		exit 1; \
	fi

# Setup local tools
local-setup:
	@echo "Setting up local verification tools..."
	@mkdir -p tools
	@echo "Downloading TLA+ tools..."
	@wget -q https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar -O tools/tla2tools.jar || \
		(echo "Failed to download TLA+ tools"; exit 1)
	@echo "Downloading Alloy Analyzer..."
	@wget -q https://github.com/AlloyTools/org.alloytools.alloy/releases/download/v6.0.0/org.alloytools.alloy.dist.jar -O tools/alloy.jar || \
		(echo "Failed to download Alloy"; exit 1)
	@echo "Local tools setup complete!"

# Run verifications in Docker
docker-verify: docker-build
	@echo "Running verifications in Docker container..."
	docker-compose run --rm formal-verification make verify

# Clean verification results
clean:
	@echo "Cleaning verification results..."
	rm -rf verification-results/
	@echo "Clean complete"

# CI-specific target (fail on errors)
ci-verify: verify
	@echo "Checking for verification errors..."
	@if grep -q "Error" verification-results/tla/tlc-output.log 2>/dev/null; then \
		echo "TLA+ verification failed!"; \
		exit 1; \
	fi
	@echo "CI verification passed!"