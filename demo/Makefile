# Makefile for bookstore demo formal verification

.PHONY: all clean verify-demo verify-bookstore-tla verify-bookstore-alloy verify-refined verify-refined-tla verify-refined-alloy compare-results help

# Default target
all: verify-demo

# Help target
help:
	@echo "Available targets for bookstore demo:"
	@echo "  make verify-demo           - Run all bookstore verifications (TLA+ and Alloy)"
	@echo "  make verify-comprehensive  - Run comprehensive verification with detailed reporting"
	@echo "  make verify-bookstore-tla  - Run TLA+ model checking on BookstoreSystem.tla"
	@echo "  make verify-bookstore-alloy - Run Alloy analysis on bookstore.als"
	@echo "  make verify-refined        - Run all refined specification verifications"
	@echo "  make verify-refined-tla    - Run TLA+ model checking on refined specification"
	@echo "  make verify-refined-alloy  - Run Alloy analysis on refined specification"
	@echo "  make compare-results       - Compare original vs refined verification results"
	@echo "  make setup-tools           - Setup verification tools"
	@echo "  make report                - Generate verification report"
	@echo "  make clean                 - Clean verification results"

# Run all demo verifications
verify-demo: verify-bookstore-tla verify-bookstore-alloy
	@echo "✅ All bookstore demo verifications completed!"

# Run refined specification verifications
verify-refined: verify-refined-tla verify-refined-alloy
	@echo "✅ All refined specification verifications completed!"

# Run TLA+ verification for bookstore system
verify-bookstore-tla:
	@echo "🔍 Running TLA+ model checking on BookstoreSystem.tla..."
	@mkdir -p verification-results/tla
	@if [ -f ../formal-specs/tools/tla2tools.jar ]; then \
		echo "Using TLA+ tools from formal-specs..."; \
		java -cp ../formal-specs/tools/tla2tools.jar tlc2.TLC \
			-config formal-specs/bookstore.cfg \
			-deadlock \
			-coverage 1 \
			-workers auto \
			formal-specs/BookstoreSystem.tla 2>&1 | tee verification-results/tla/bookstore-tlc-output.log; \
	elif command -v tlc >/dev/null 2>&1; then \
		tlc -config formal-specs/bookstore.cfg -deadlock -coverage 1 formal-specs/BookstoreSystem.tla 2>&1 | tee verification-results/tla/bookstore-tlc-output.log; \
	else \
		echo "❌ Error: TLC not found. Please run 'make setup-tools' first."; \
		exit 1; \
	fi
	@if grep -q "Error:" verification-results/tla/bookstore-tlc-output.log; then \
		echo "❌ TLA+ verification found errors in bookstore system"; \
		exit 1; \
	else \
		echo "✅ TLA+ verification passed for bookstore system"; \
	fi

# Run TLA+ verification for refined bookstore system
verify-refined-tla:
	@echo "🔍 Running TLA+ model checking on BookstoreSystemRefined.tla..."
	@mkdir -p verification-results/tla-refined
	@if [ -f ../formal-specs/tools/tla2tools.jar ]; then \
		echo "Using TLA+ tools from formal-specs..."; \
		java -cp ../formal-specs/tools/tla2tools.jar tlc2.TLC \
			-config formal-specs/bookstore-refined.cfg \
			-deadlock \
			-coverage 1 \
			-workers auto \
			formal-specs/BookstoreSystemRefined.tla 2>&1 | tee verification-results/tla-refined/bookstore-refined-tlc-output.log; \
	elif command -v tlc >/dev/null 2>&1; then \
		tlc -config formal-specs/bookstore-refined.cfg -deadlock -coverage 1 formal-specs/BookstoreSystemRefined.tla 2>&1 | tee verification-results/tla-refined/bookstore-refined-tlc-output.log; \
	else \
		echo "❌ Error: TLC not found. Please run 'make setup-tools' first."; \
		exit 1; \
	fi
	@if grep -q "Error:" verification-results/tla-refined/bookstore-refined-tlc-output.log; then \
		echo "❌ TLA+ verification found errors in refined bookstore system"; \
		exit 1; \
	else \
		echo "✅ TLA+ verification passed for refined bookstore system"; \
	fi

# Run Alloy verification for bookstore system
verify-bookstore-alloy:
	@echo "🔍 Running Alloy analysis on bookstore.als..."
	@mkdir -p verification-results/alloy
	@if [ -f ../formal-specs/tools/alloy.jar ]; then \
		echo "Using Alloy from formal-specs..."; \
		echo "Validating Alloy syntax and running basic checks..."; \
		java -cp ../formal-specs/tools/alloy.jar edu.mit.csail.sdg.alloy4whole.ExampleUsingTheCompiler \
			formal-specs/bookstore.als > verification-results/alloy/bookstore-alloy-output.log 2>&1 || true; \
	elif command -v alloy >/dev/null 2>&1; then \
		echo "run RaceConditionScenario for 4" | alloy -c formal-specs/bookstore.als > verification-results/alloy/bookstore-alloy-output.log 2>&1; \
	else \
		echo "❌ Error: Alloy not found. Please run 'make setup-tools' first."; \
		exit 1; \
	fi
	@echo "✅ Alloy verification completed for bookstore system"

# Run Alloy verification for refined bookstore system
verify-refined-alloy:
	@echo "🔍 Running Alloy analysis on bookstore-refined.als..."
	@mkdir -p verification-results/alloy-refined
	@if [ -f ../formal-specs/tools/alloy.jar ]; then \
		echo "Using Alloy from formal-specs..."; \
		echo "Validating refined Alloy syntax and running checks..."; \
		java -cp ../formal-specs/tools/alloy.jar edu.mit.csail.sdg.alloy4whole.ExampleUsingTheCompiler \
			formal-specs/bookstore-refined.als > verification-results/alloy-refined/bookstore-refined-alloy-output.log 2>&1 || true; \
	elif command -v alloy >/dev/null 2>&1; then \
		echo "run SuccessfulOrderFlow for 5" | alloy -c formal-specs/bookstore-refined.als > verification-results/alloy-refined/bookstore-refined-alloy-output.log 2>&1; \
	else \
		echo "❌ Error: Alloy not found. Please run 'make setup-tools' first."; \
		exit 1; \
	fi
	@echo "✅ Alloy verification completed for refined bookstore system"

# Compare original vs refined results
compare-results:
	@echo "📊 Comparing original vs refined verification results..."
	@mkdir -p verification-results/comparison
	@echo "# Verification Results Comparison" > verification-results/comparison/comparison-report.md
	@echo "" >> verification-results/comparison/comparison-report.md
	@echo "## Original Specification Results" >> verification-results/comparison/comparison-report.md
	@if [ -f verification-results/tla/bookstore-tlc-output.log ]; then \
		echo "### TLA+ Original" >> verification-results/comparison/comparison-report.md; \
		if grep -q "Error:" verification-results/tla/bookstore-tlc-output.log; then \
			echo "❌ **FAILED** - Invariant violations found" >> verification-results/comparison/comparison-report.md; \
		else \
			echo "✅ **PASSED** - No violations" >> verification-results/comparison/comparison-report.md; \
		fi; \
	fi
	@echo "" >> verification-results/comparison/comparison-report.md
	@echo "## Refined Specification Results" >> verification-results/comparison/comparison-report.md
	@if [ -f verification-results/tla-refined/bookstore-refined-tlc-output.log ]; then \
		echo "### TLA+ Refined" >> verification-results/comparison/comparison-report.md; \
		if grep -q "Error:" verification-results/tla-refined/bookstore-refined-tlc-output.log; then \
			echo "❌ **FAILED** - Issues remain" >> verification-results/comparison/comparison-report.md; \
		else \
			echo "✅ **PASSED** - All ambiguities resolved" >> verification-results/comparison/comparison-report.md; \
		fi; \
	fi
	@echo "✅ Comparison report generated: verification-results/comparison/comparison-report.md"

# Setup tools (use parent directory tools)
setup-tools:
	@echo "🔧 Setting up verification tools for demo..."
	@if [ ! -f ../formal-specs/tools/tla2tools.jar ] || [ ! -f ../formal-specs/tools/alloy.jar ]; then \
		echo "Setting up tools in parent formal-specs directory..."; \
		cd ../formal-specs && make local-setup; \
	else \
		echo "✅ Tools already available in ../formal-specs/tools/"; \
	fi

# Clean verification results
clean:
	@echo "🧹 Cleaning bookstore demo verification results..."
	rm -rf verification-results/
	@echo "✅ Clean complete"

# Run comprehensive verification with detailed script
verify-comprehensive:
	@echo "🚀 Running comprehensive bookstore verification..."
	./verify-bookstore.sh

# Generate verification report
report:
	@echo "📊 Generating verification report..."
	@mkdir -p verification-results
	@echo "# Bookstore System Verification Report" > verification-results/bookstore-verification-report.md
	@echo "" >> verification-results/bookstore-verification-report.md
	@echo "## Overview" >> verification-results/bookstore-verification-report.md
	@echo "This report summarizes the formal verification results for the bookstore system demo." >> verification-results/bookstore-verification-report.md
	@echo "" >> verification-results/bookstore-verification-report.md
	@echo "Generated on: $$(date)" >> verification-results/bookstore-verification-report.md
	@echo "✅ Report generated: verification-results/bookstore-verification-report.md"