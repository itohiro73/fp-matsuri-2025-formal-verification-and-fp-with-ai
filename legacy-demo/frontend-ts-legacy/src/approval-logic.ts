// Legacy approval logic with problematic patterns

interface User {
    id: number;
    name: string;
    role: string; // Problem: Should be enum/union type
    manager?: number; // Problem: Optional manager can cause null reference errors
}

interface Expense {
    id?: number; // Problem: Optional ID can cause issues
    applicant: number;
    amount: number;
    status: string; // Problem: Should be enum/union type
    approvals?: any[]; // Problem: Using any[] loses type safety
}

class ApprovalEngine {
    private users: User[] = []; // Problem: Mutable array
    private expenses: Expense[] = []; // Problem: Mutable array
    
    constructor() {
        // Problem: Side effect in constructor
        this.loadUsers();
        this.loadExpenses();
    }

    // Problem: Synchronous operation that should be async
    private loadUsers() {
        // Problem: Hard-coded test data
        this.users = [
            {id: 1, name: "Employee1", role: "employee", manager: 2},
            {id: 2, name: "Manager1", role: "manager", manager: 3},
            {id: 3, name: "Director1", role: "director", manager: 4},
            {id: 4, name: "FinanceDirector", role: "finance_director"}
        ];
    }

    // Problem: Synchronous operation that should be async
    private loadExpenses() {
        this.expenses = [];
    }

    // Problem: No error handling
    canApprove(userId: number, expenseId: number): boolean {
        const user = this.users.find(u => u.id === userId);
        const expense = this.expenses.find(e => e.id === expenseId);
        
        // Problem: No null checking
        if (!user || !expense) {
            return false; // Problem: Silent failure
        }

        // Problem: Self-approval not properly prevented
        if (user.id === expense.applicant) {
            // Problem: This check is insufficient
            return false;
        }

        // Problem: Complex nested logic hard to understand
        if (expense.amount <= 10000) {
            return user.role === "manager" && this.isManagerOf(userId, expense.applicant);
        } else if (expense.amount <= 50000) {
            if (user.role === "manager") {
                return this.isManagerOf(userId, expense.applicant) && !this.hasManagerApproval(expenseId);
            } else if (user.role === "director") {
                return this.hasManagerApproval(expenseId) && this.isDirectorOf(userId, expense.applicant);
            }
        } else {
            // Problem: Duplicated logic
            if (user.role === "manager") {
                return this.isManagerOf(userId, expense.applicant) && !this.hasManagerApproval(expenseId);
            } else if (user.role === "director") {
                return this.hasManagerApproval(expenseId) && !this.hasDirectorApproval(expenseId);
            } else if (user.role === "finance_director") {
                return this.hasManagerApproval(expenseId) && this.hasDirectorApproval(expenseId);
            }
        }
        
        return false;
    }

    // Problem: No error handling for invalid IDs
    private isManagerOf(managerId: number, employeeId: number): boolean {
        const employee = this.users.find(u => u.id === employeeId);
        return employee?.manager === managerId; // Problem: Unsafe optional chaining
    }

    // Problem: Inefficient lookup
    private isDirectorOf(directorId: number, employeeId: number): boolean {
        const employee = this.users.find(u => u.id === employeeId);
        if (!employee || !employee.manager) return false;
        
        const manager = this.users.find(u => u.id === employee.manager);
        return manager?.manager === directorId;
    }

    // Problem: Side effect in query method
    private hasManagerApproval(expenseId: number): boolean {
        const expense = this.expenses.find(e => e.id === expenseId);
        if (!expense?.approvals) {
            expense!.approvals = []; // Problem: Mutating state in read operation
            return false;
        }
        
        // Problem: Type casting without checking
        return expense.approvals.some((approval: any) => 
            this.users.find(u => u.id === approval.approverId)?.role === "manager");
    }

    private hasDirectorApproval(expenseId: number): boolean {
        const expense = this.expenses.find(e => e.id === expenseId);
        if (!expense?.approvals) return false;
        
        return expense.approvals.some((approval: any) => 
            this.users.find(u => u.id === approval.approverId)?.role === "director");
    }

    // Problem: Mutates global state
    async approve(userId: number, expenseId: number, comment: string) {
        if (!this.canApprove(userId, expenseId)) {
            throw new Error("Cannot approve"); // Problem: Generic error message
        }

        const expense = this.expenses.find(e => e.id === expenseId);
        const user = this.users.find(u => u.id === userId);
        
        // Problem: No null checking before use
        if (!expense!.approvals) {
            expense!.approvals = [];
        }

        // Problem: Direct mutation of array
        expense!.approvals.push({
            approverId: userId,
            timestamp: Date.now(),
            action: "approve",
            comment: comment
        });

        // Problem: Side effect in business logic
        this.updateExpenseStatus(expenseId);
        
        // Problem: No return value for success/failure
    }

    // Problem: Complex status update logic
    private updateExpenseStatus(expenseId: number) {
        const expense = this.expenses.find(e => e.id === expenseId);
        if (!expense) return;

        const hasManager = this.hasManagerApproval(expenseId);
        const hasDirector = this.hasDirectorApproval(expenseId);
        const hasFinance = expense.approvals?.some((approval: any) => 
            this.users.find(u => u.id === approval.approverId)?.role === "finance_director");

        // Problem: Complex nested conditions
        if (expense.amount <= 10000) {
            if (hasManager) {
                expense.status = "approved"; // Problem: Direct mutation
            }
        } else if (expense.amount <= 50000) {
            if (hasManager && hasDirector) {
                expense.status = "approved";
            } else if (hasManager) {
                expense.status = "director_review";
            }
        } else {
            if (hasManager && hasDirector && hasFinance) {
                expense.status = "approved";
            } else if (hasManager && hasDirector) {
                expense.status = "finance_review";
            } else if (hasManager) {
                expense.status = "director_review";
            }
        }
    }

    // Problem: Synchronous operation that could be slow
    getAllPendingApprovals(userId: number): Expense[] {
        return this.expenses.filter(expense => 
            this.canApprove(userId, expense.id!) && expense.status !== "approved"
        ); // Problem: Returns mutable array
    }

    // Problem: No input validation
    reject(userId: number, expenseId: number, comment: string) {
        const expense = this.expenses.find(e => e.id === expenseId);
        
        // Problem: No authorization check
        expense!.status = "rejected"; // Problem: Direct mutation without checking
        
        if (!expense!.approvals) {
            expense!.approvals = [];
        }

        expense!.approvals.push({
            approverId: userId,
            timestamp: Date.now(),
            action: "reject",
            comment: comment
        });
    }
}

// Problem: Global singleton instance
export const approvalEngine = new ApprovalEngine();