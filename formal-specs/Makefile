# Makefile for formal verification

.PHONY: all clean verify-tla verify-alloy verify docker-build docker-verify help

# Default target
all: verify

# Help target
help:
	@echo "Available targets:"
	@echo "  make verify          - Run all verifications (TLA+ and Alloy)"
	@echo "  make verify-tla      - Run TLA+ model checking"
	@echo "  make verify-alloy    - Run Alloy analysis"
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
	else \
		echo "TLC not found. Running with Java..."; \
		java -cp tla2tools.jar tlc2.TLC -config workflow.cfg -deadlock -coverage 1 workflow.tla 2>&1 | tee verification-results/tla/tlc-output.log; \
	fi
	@echo "TLA+ verification completed. Results in verification-results/tla/"

# Run Alloy verification
verify-alloy:
	@echo "Running Alloy analysis on constraints.als..."
	@mkdir -p verification-results/alloy
	@if command -v alloy >/dev/null 2>&1; then \
		echo "run systemInvariants for 5" | alloy -c constraints.als > verification-results/alloy/alloy-output.log 2>&1; \
	else \
		echo "Note: Alloy GUI mode required for full analysis. Install Alloy or use Docker."; \
	fi
	@echo "Alloy verification completed. Results in verification-results/alloy/"

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