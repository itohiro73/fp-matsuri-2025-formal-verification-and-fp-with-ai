# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

This is a demonstration project for **2025 FP祭り** presentation: "AIと共に進化する開発手法：形式手法と関数型プログラミングの可能性" (AI-Driven Development Evolution: The Potential of Formal Methods and Functional Programming).

The project demonstrates a **corporate expense application system** to contrast traditional development approaches with "formal methods + functional programming + AI-driven development".

## Key Architecture Philosophy

- **Formal Methods**: TLA+ for workflow state transitions, Alloy for constraint modeling
- **Functional Programming**: Type-safe, side-effect-free implementations
- **AI-Driven Development**: Leveraging AI agents (Cursor, Cline, Devin) for optimal code generation

## Project Structure

The project is organized into 5 development phases:

1. **Phase 1**: Formal specifications (`formal-specs/`, `docs/`)
2. **Phase 2**: Functional backend (`functional-demo/backend-kotlin/`)
3. **Phase 3**: Functional frontend (`functional-demo/frontend-react/`)
4. **Phase 4**: AI-generated code (`ai-generation/`)
5. **Phase 5**: Presentation materials (`presentation/`)

## Domain Model: Expense Application System

### Core Entities
- **Expense**: ID, applicant, amount, type, description, status, timestamp
- **User**: ID, name, email, role, manager
- **ApprovalHistory**: approver, timestamp, action, comment

### Approval Flow Rules
- ≤10,000円: Direct manager only
- 10,001-50,000円: Manager → Director
- ≥50,001円: Manager → Director → Finance Director

### Critical Business Constraints
- No self-approval
- Sequential approval order enforced
- Only managers can approve subordinates
- 72-hour auto-escalation
- 2-week approval deadline

## Technology Stack

### Backend
- **Kotlin + Spring Boot**
- **Arrow-kt**: Functional programming library
- **PostgreSQL**: Database
- **Gradle**: Build tool

### Frontend
- **React + TypeScript**
- **fp-ts**: Functional programming library
- **Vite**: Build tool

### Formal Methods
- **TLA+**: State transition specification
- **Alloy**: Constraint verification
- **Design by Contract**: Preconditions/postconditions

## Development Approach

When implementing features:

1. **Start with formal specifications** (TLA+/Alloy) before coding
2. **Use sealed classes** for type-safe state modeling in Kotlin
3. **Implement pure functions** with clear contracts
4. **Leverage Either/Option types** for error handling
5. **Generate code from specifications** when possible

## AI Development Context

This project specifically demonstrates how formal methods and functional programming provide:
- **Framework for AI**: Clear specifications improve AI code generation accuracy
- **Context minimization**: Side-effect isolation makes code easier for AI to understand
- **Type safety**: Compile-time verification catches AI-generated errors early

## Important Notes

- Code should demonstrate **contrast between traditional and formal/functional approaches**
- Implementations should be **AI-generation friendly** with clear specifications
- All code should follow **functional programming principles** (immutability, pure functions)
- **Document AI prompts used** in `ai-generation/prompts-used.md`