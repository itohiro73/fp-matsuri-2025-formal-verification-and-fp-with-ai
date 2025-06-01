// Legacy expense form implementation with intentional problems

class ExpenseForm {
    private expense: any; // Problem: Using 'any' type loses type safety

    constructor() {
        this.expense = {}; // Problem: Uninitialized object can have missing properties
    }

    // Problem: No input validation
    setApplicant(applicant: string) {
        this.expense.applicant = applicant;
    }

    // Problem: Amount can be negative or zero
    setAmount(amount: number) {
        this.expense.amount = amount;
    }

    // Problem: Type is not validated against enum
    setType(type: string) {
        this.expense.type = type;
    }

    setDescription(description: string) {
        this.expense.description = description;
    }

    // Problem: No validation before submission
    async submit(): Promise<any> {
        try {
            // Problem: Direct mutation of state
            this.expense.status = "submitted";
            this.expense.submitTime = new Date().getTime();
            
            // Problem: No error handling for network failures
            const response = await fetch("/api/expenses", {
                method: "POST",
                headers: {
                    "Content-Type": "application/json"
                },
                body: JSON.stringify(this.expense)
            });

            // Problem: Assumes response is always JSON
            const result = await response.json();
            
            // Problem: No status code checking
            return result;
        } catch (error) {
            // Problem: Generic error handling
            console.log("Error occurred");
            throw error;
        }
    }

    // Problem: Can edit after submission
    edit(field: string, value: any) {
        this.expense[field] = value; // Problem: No type checking
    }

    // Problem: Exposes internal state directly
    getExpense() {
        return this.expense; // Problem: Returns mutable reference
    }

    // Problem: Inconsistent state management
    reset() {
        this.expense = {}; // Problem: Doesn't reset to proper initial state
    }

    // Problem: Side effect in getter
    getStatus() {
        if (!this.expense.status) {
            this.expense.status = "draft"; // Problem: Mutating state in getter
        }
        return this.expense.status;
    }

    // Problem: Complex validation logic mixed with business logic
    isValid() {
        // Problem: No clear validation rules
        return this.expense.applicant && 
               this.expense.amount && 
               this.expense.type;
        // Problem: Missing many validation rules (amount > 0, etc.)
    }

    // Problem: Synchronous operation that could fail
    calculateApprovalPath() {
        let path = [];
        
        // Problem: Hard-coded business logic
        if (this.expense.amount <= 10000) {
            path.push("manager");
        } else if (this.expense.amount <= 50000) {
            path.push("manager");
            path.push("director");
        } else {
            path.push("manager");
            path.push("director");
            path.push("finance_director");
        }
        
        // Problem: Returns array that can be mutated
        return path;
    }
}

// Problem: Global state
let currentExpense: ExpenseForm | null = null;

// Problem: Side effects in initialization
function initializeExpenseForm() {
    currentExpense = new ExpenseForm();
    // Problem: DOM manipulation mixed with business logic
    document.getElementById("expense-form")?.addEventListener("submit", async (e) => {
        e.preventDefault();
        
        // Problem: Casting without type checking
        const applicant = (document.getElementById("applicant") as HTMLInputElement).value;
        const amount = parseInt((document.getElementById("amount") as HTMLInputElement).value);
        const type = (document.getElementById("type") as HTMLSelectElement).value;
        const description = (document.getElementById("description") as HTMLTextAreaElement).value;
        
        // Problem: No validation
        currentExpense!.setApplicant(applicant);
        currentExpense!.setAmount(amount);
        currentExpense!.setType(type);
        currentExpense!.setDescription(description);
        
        try {
            // Problem: Blocking UI during submission
            await currentExpense!.submit();
            alert("Expense submitted successfully"); // Problem: Alert in business logic
        } catch (error) {
            alert("Failed to submit expense"); // Problem: Generic error message
        }
    });
}

// Problem: Automatic execution on module load
initializeExpenseForm();