#!/bin/bash

# Local verification script for running TLA+ and Alloy without Docker
# For use on systems where Docker is not available (e.g., Android/Termux)

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
TOOLS_DIR="$SCRIPT_DIR/tools"

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

# Check if Java is installed
if ! command -v java &> /dev/null; then
    echo -e "${RED}Error: Java is not installed. Please install Java 8 or higher.${NC}"
    exit 1
fi

echo -e "${GREEN}=== Formal Verification Tools (Local) ===${NC}"
echo -e "Java version:"
java -version 2>&1 | head -n 1

# Check if tools are downloaded
if [ ! -f "$TOOLS_DIR/tla2tools.jar" ]; then
    echo -e "${RED}Error: TLA+ tools not found. Please download tla2tools.jar to $TOOLS_DIR/${NC}"
    exit 1
fi

if [ ! -f "$TOOLS_DIR/alloy.jar" ]; then
    echo -e "${RED}Error: Alloy Analyzer not found. Please download alloy.jar to $TOOLS_DIR/${NC}"
    exit 1
fi

# Function to run TLA+ model checking
run_tlc() {
    local spec_file=$1
    local config_file=$2
    
    echo -e "\n${YELLOW}Running TLA+ model checking on $spec_file...${NC}"
    
    if [ ! -f "$spec_file" ]; then
        echo -e "${RED}Error: TLA+ specification file not found: $spec_file${NC}"
        return 1
    fi
    
    if [ ! -f "$config_file" ]; then
        echo -e "${RED}Error: TLA+ configuration file not found: $config_file${NC}"
        return 1
    fi
    
    # Run TLC model checker with reduced memory
    java -Xmx512m -XX:+UseParallelGC -cp "$TOOLS_DIR/tla2tools.jar" tlc2.TLC \
        -config "$config_file" \
        -workers 2 \
        -fp 1 \
        "$spec_file"
    
    if [ $? -eq 0 ]; then
        echo -e "${GREEN}✓ TLA+ model checking passed${NC}"
        return 0
    else
        echo -e "${RED}✗ TLA+ model checking failed${NC}"
        return 1
    fi
}

# Function to run Alloy analysis
run_alloy() {
    local spec_file=$1
    
    echo -e "\n${YELLOW}Running Alloy analysis on $spec_file...${NC}"
    
    if [ ! -f "$spec_file" ]; then
        echo -e "${RED}Error: Alloy specification file not found: $spec_file${NC}"
        return 1
    fi
    
    # Run Alloy in batch mode (command-line analysis)
    # Note: This runs a basic satisfiability check. For full analysis, use the GUI
    java -cp "$TOOLS_DIR/alloy.jar" edu.mit.csail.sdg.alloy4whole.ExampleUsingTheCompiler "$spec_file"
    
    if [ $? -eq 0 ]; then
        echo -e "${GREEN}✓ Alloy analysis completed${NC}"
        return 0
    else
        echo -e "${RED}✗ Alloy analysis failed${NC}"
        return 1
    fi
}

# Main verification process
main() {
    local failed=0
    
    echo -e "${GREEN}Starting formal verification...${NC}"
    
    # Run TLA+ verification
    if [ -f "$SCRIPT_DIR/workflow.tla" ] && [ -f "$SCRIPT_DIR/workflow.cfg" ]; then
        if ! run_tlc "$SCRIPT_DIR/workflow.tla" "$SCRIPT_DIR/workflow.cfg"; then
            failed=$((failed + 1))
        fi
    else
        echo -e "${YELLOW}Warning: TLA+ files not found, skipping TLA+ verification${NC}"
    fi
    
    # Run Alloy verification
    if [ -f "$SCRIPT_DIR/constraints.als" ]; then
        if ! run_alloy "$SCRIPT_DIR/constraints.als"; then
            failed=$((failed + 1))
        fi
    else
        echo -e "${YELLOW}Warning: Alloy file not found, skipping Alloy verification${NC}"
    fi
    
    # Summary
    echo -e "\n${GREEN}=== Verification Summary ===${NC}"
    if [ $failed -eq 0 ]; then
        echo -e "${GREEN}✓ All verifications passed!${NC}"
        exit 0
    else
        echo -e "${RED}✗ $failed verification(s) failed${NC}"
        exit 1
    fi
}

# Check for command-line arguments
if [ "$1" == "--help" ] || [ "$1" == "-h" ]; then
    echo "Usage: $0 [tla|alloy]"
    echo ""
    echo "Run formal verification tools locally (without Docker)"
    echo ""
    echo "Options:"
    echo "  tla    - Run only TLA+ verification"
    echo "  alloy  - Run only Alloy verification"
    echo "  (none) - Run all verifications"
    exit 0
fi

# Run specific verification or all
case "$1" in
    tla)
        run_tlc "$SCRIPT_DIR/workflow.tla" "$SCRIPT_DIR/workflow.cfg"
        ;;
    alloy)
        run_alloy "$SCRIPT_DIR/constraints.als"
        ;;
    *)
        main
        ;;
esac