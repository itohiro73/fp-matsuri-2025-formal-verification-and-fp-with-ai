// Legacy state management with problematic patterns

// Problem: Global mutable state
let globalState: any = {
    currentUser: null,
    expenses: [],
    users: [],
    isLoading: false,
    error: null
};

// Problem: No type safety for state
interface AppState {
    currentUser: any; // Problem: Using any
    expenses: any[]; // Problem: Using any[]
    users: any[]; // Problem: Using any[]
    isLoading: boolean;
    error: string | null;
}

class StateManager {
    private listeners: Function[] = []; // Problem: No type for listener functions
    
    constructor() {
        // Problem: Side effect in constructor
        this.initializeState();
    }

    // Problem: Synchronous initialization
    private initializeState() {
        globalState = {
            currentUser: null,
            expenses: [],
            users: [],
            isLoading: false,
            error: null
        };
    }

    // Problem: Direct access to mutable state
    getState(): any {
        return globalState; // Problem: Returns mutable reference
    }

    // Problem: No validation of state updates
    setState(newState: Partial<any>) {
        // Problem: Direct mutation
        Object.assign(globalState, newState);
        
        // Problem: Synchronous notification
        this.notifyListeners();
    }

    // Problem: No type checking for listeners
    subscribe(listener: Function) {
        this.listeners.push(listener);
        
        // Problem: No way to unsubscribe properly
        return () => {
            const index = this.listeners.indexOf(listener);
            if (index > -1) {
                this.listeners.splice(index, 1);
            }
        };
    }

    private notifyListeners() {
        // Problem: Synchronous execution could block UI
        this.listeners.forEach(listener => {
            try {
                listener(globalState);
            } catch (error) {
                // Problem: Silent error handling
                console.error("Listener error:", error);
            }
        });
    }

    // Problem: Business logic mixed with state management
    async loadExpenses() {
        this.setState({ isLoading: true, error: null });
        
        try {
            // Problem: Hard-coded URL
            const response = await fetch("/api/expenses");
            
            // Problem: No status checking
            const expenses = await response.json();
            
            // Problem: Direct mutation
            this.setState({ 
                expenses: expenses, 
                isLoading: false 
            });
            
        } catch (error) {
            // Problem: Generic error handling
            this.setState({ 
                error: "Failed to load expenses", 
                isLoading: false 
            });
        }
    }

    // Problem: No input validation
    addExpense(expense: any) {
        const currentExpenses = globalState.expenses;
        
        // Problem: Direct array mutation
        currentExpenses.push(expense);
        
        this.setState({ expenses: currentExpenses });
    }

    // Problem: Linear search, inefficient
    updateExpense(expenseId: number, updates: any) {
        const expenses = globalState.expenses;
        const index = expenses.findIndex((e: any) => e.id === expenseId);
        
        if (index >= 0) {
            // Problem: Direct mutation of array element
            Object.assign(expenses[index], updates);
            this.setState({ expenses: expenses });
        }
    }

    // Problem: No error handling
    deleteExpense(expenseId: number) {
        const expenses = globalState.expenses;
        const filteredExpenses = expenses.filter((e: any) => e.id !== expenseId);
        
        this.setState({ expenses: filteredExpenses });
    }

    // Problem: Synchronous operation
    getCurrentUser() {
        return globalState.currentUser;
    }

    // Problem: No authentication validation
    setCurrentUser(user: any) {
        this.setState({ currentUser: user });
        
        // Problem: Side effect in setter
        localStorage.setItem("currentUser", JSON.stringify(user));
    }

    // Problem: Complex derived state calculation
    getPendingExpenses() {
        const user = this.getCurrentUser();
        if (!user) return [];
        
        // Problem: Inefficient filtering
        return globalState.expenses.filter((expense: any) => {
            // Problem: Business logic in state manager
            if (user.role === "manager") {
                return expense.status === "manager_review" && 
                       this.isManagerOf(user.id, expense.applicant);
            } else if (user.role === "director") {
                return expense.status === "director_review";
            } else if (user.role === "finance_director") {
                return expense.status === "finance_review";
            }
            return false;
        });
    }

    // Problem: Duplicated business logic
    private isManagerOf(managerId: number, employeeId: number): boolean {
        const users = globalState.users;
        const employee = users.find((u: any) => u.id === employeeId);
        return employee?.manager === managerId;
    }

    // Problem: No error boundaries
    getExpenseById(id: number) {
        const expense = globalState.expenses.find((e: any) => e.id === id);
        return expense; // Problem: Could return undefined
    }

    // Problem: Side effect in getter
    getExpenseStats() {
        const expenses = globalState.expenses;
        
        // Problem: Mutation during calculation
        if (!globalState.cachedStats) {
            globalState.cachedStats = {
                total: expenses.length,
                approved: expenses.filter((e: any) => e.status === "approved").length,
                pending: expenses.filter((e: any) => e.status !== "approved" && e.status !== "rejected").length,
                rejected: expenses.filter((e: any) => e.status === "rejected").length
            };
        }
        
        return globalState.cachedStats;
    }

    // Problem: Race condition possible
    async refreshState() {
        this.setState({ isLoading: true });
        
        try {
            // Problem: Multiple concurrent requests
            const [expensesResponse, usersResponse] = await Promise.all([
                fetch("/api/expenses"),
                fetch("/api/users")
            ]);
            
            const expenses = await expensesResponse.json();
            const users = await usersResponse.json();
            
            // Problem: Batch update that could be inconsistent
            this.setState({
                expenses: expenses,
                users: users,
                isLoading: false,
                error: null
            });
            
        } catch (error) {
            this.setState({
                isLoading: false,
                error: "Failed to refresh data"
            });
        }
    }

    // Problem: No cleanup
    destroy() {
        // Problem: Doesn't clean up properly
        this.listeners = [];
        globalState = null;
    }
}

// Problem: Global singleton
export const stateManager = new StateManager();

// Problem: Direct export of mutable state
export { globalState };