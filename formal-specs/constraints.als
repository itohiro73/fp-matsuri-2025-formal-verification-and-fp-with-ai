// Alloy model for expense application system constraints
module ExpenseConstraints

// Basic signatures
abstract sig User {
    name: one String,
    email: one String,
    role: one Role,
    manages: set User  // Changed from manager to manages for clarity
}

abstract sig Role {}
one sig Employee, Manager, Director, FinanceDirector extends Role {}

sig ExpenseType {}
one sig Travel, Accommodation, Meeting, Equipment extends ExpenseType {}

sig ExpenseStatus {}
one sig Draft, Submitted, ManagerReview, DirectorReview, 
         FinanceReview, Approved, Rejected extends ExpenseStatus {}

sig Expense {
    id: one Int,
    applicant: one User,
    amount: one Int,
    expenseType: one ExpenseType,
    description: one String,
    status: one ExpenseStatus,
    submitTime: one Int
}

sig Approval {
    expense: one Expense,
    approver: one User,
    timestamp: one Int,
    action: one ApprovalAction,
    comment: one String
}

abstract sig ApprovalAction {}
one sig Approve, Reject extends ApprovalAction {}

// ====================== CONSTRAINTS ======================

// Basic structural constraints
fact UserHierarchy {
    // No user can manage themselves
    no u: User | u in u.manages
    
    // Management relationship is acyclic
    no u: User | u in u.^manages
    
    // Role hierarchy constraints
    all u: User | u.role = Manager implies some subordinate: User | subordinate in u.manages
    all u: User | u.role = Director implies some manager: User | manager in u.manages and manager.role = Manager
    all u: User | u.role = FinanceDirector implies u.role != Employee
}

fact ExpenseConstraints {
    // Amount must be positive
    all e: Expense | e.amount > 0
    
    // Amount has reasonable upper bound (10 million yen)
    all e: Expense | e.amount <= 10000000
    
    // Submit time must be non-negative
    all e: Expense | e.submitTime >= 0
    
    // Each expense has unique ID
    all disj e1, e2: Expense | e1.id != e2.id
}

fact ApprovalConstraints {
    // Approval timestamp must be after or equal to expense submit time
    all a: Approval | a.timestamp >= a.expense.submitTime
    
    // Approvals for same expense must have increasing timestamps
    all disj a1, a2: Approval | 
        a1.expense = a2.expense and a1.timestamp < a2.timestamp implies
        a1.timestamp != a2.timestamp
}

// ====================== APPROVAL RULES ======================

// Define required approval path based on amount
fun requiredApprovers[e: Expense]: set User {
    e.amount <= 10000 implies 
        // Only direct manager needed
        e.applicant.manages
    else e.amount <= 50000 implies
        // Manager then director
        e.applicant.manages + (e.applicant.^manages & role.Director)
    else
        // Manager, director, then finance director  
        e.applicant.manages + (e.applicant.^manages & role.Director) + role.FinanceDirector
}

// ====================== BUSINESS RULES ======================

// Rule 1: No self-approval
fact NoSelfApproval {
    all a: Approval | a.approver != a.expense.applicant
}

// Rule 2: Only authorized users can approve
fact OnlyAuthorizedApprovers {
    all a: Approval | {
        // Manager level approval
        (a.expense.amount <= 10000 and a.approver.role = Manager and 
         a.approver in a.expense.applicant.manages) or
        
        // Director level approval
        (a.expense.amount > 10000 and a.expense.amount <= 50000 and 
         a.approver.role = Director and 
         a.approver in a.expense.applicant.^manages) or
         
        // Finance director level approval
        (a.expense.amount > 50000 and a.approver.role = FinanceDirector)
    }
}

// Rule 3: Sequential approval order
fact SequentialApproval {
    all e: Expense | {
        let approvals = e.~expense | {
            // Sort approvals by timestamp
            all disj a1, a2: approvals | a1.timestamp < a2.timestamp implies {
                // If manager approval required, it must come first
                (e.amount > 0 and a1.approver.role = Manager) implies
                    a2.approver.role in (Director + FinanceDirector)
                
                // If director approval required, it must come after manager
                (e.amount > 10000 and a1.approver.role = Director) implies
                    a2.approver.role = FinanceDirector
            }
        }
    }
}

// Rule 4: Approval completeness
fact ApprovalCompleteness {
    all e: Expense | e.status = Approved implies {
        // For low amounts (<=10k): only manager approval needed
        (e.amount <= 10000 implies 
            one a: Approval | a.expense = e and a.approver.role = Manager and a.action = Approve) and
        
        // For medium amounts (10k-50k): manager + director approval needed  
        (e.amount > 10000 and e.amount <= 50000 implies
            (one a: Approval | a.expense = e and a.approver.role = Manager and a.action = Approve) and
            (one a: Approval | a.expense = e and a.approver.role = Director and a.action = Approve)) and
            
        // For high amounts (>50k): manager + director + finance director approval needed
        (e.amount > 50000 implies
            (one a: Approval | a.expense = e and a.approver.role = Manager and a.action = Approve) and
            (one a: Approval | a.expense = e and a.approver.role = Director and a.action = Approve) and
            (one a: Approval | a.expense = e and a.approver.role = FinanceDirector and a.action = Approve))
    }
}

// Rule 5: Rejection stops approval process
fact RejectionStopsProcess {
    all e: Expense | {
        (some a: Approval | a.expense = e and a.action = Reject) implies 
        e.status = Rejected
    }
}

// Rule 6: Status consistency
fact StatusConsistency {
    all e: Expense | {
        // Draft status: no approvals
        e.status = Draft implies no a: Approval | a.expense = e
        
        // Submitted status: no approvals yet
        e.status = Submitted implies no a: Approval | a.expense = e
        
        // ManagerReview status: waiting for manager approval
        e.status = ManagerReview implies {
            no a: Approval | a.expense = e and a.approver.role = Manager
            some mgr: User | mgr.role = Manager and mgr in e.applicant.manages
        }
        
        // DirectorReview status: manager approved, waiting for director
        e.status = DirectorReview implies {
            one a: Approval | a.expense = e and a.approver.role = Manager and a.action = Approve
            no a: Approval | a.expense = e and a.approver.role = Director
        }
        
        // FinanceReview status: manager and director approved, waiting for finance director
        e.status = FinanceReview implies {
            one a: Approval | a.expense = e and a.approver.role = Manager and a.action = Approve
            one a: Approval | a.expense = e and a.approver.role = Director and a.action = Approve
            no a: Approval | a.expense = e and a.approver.role = FinanceDirector
        }
    }
}

// ====================== PREDICATES FOR TESTING ======================

// Predicate: Valid expense submission
pred validExpenseSubmission[e: Expense] {
    e.status = Submitted
    e.amount > 0
    e.amount <= 10000000
    e.applicant.role = Employee
}

// Predicate: Valid approval action
pred validApprovalAction[a: Approval] {
    // No self-approval
    a.approver != a.expense.applicant
    
    // Appropriate role for amount
    (a.expense.amount <= 10000 and a.approver.role = Manager) or
    (a.expense.amount > 10000 and a.expense.amount <= 50000 and a.approver.role in (Manager + Director)) or
    (a.expense.amount > 50000 and a.approver.role in (Manager + Director + FinanceDirector))
    
    // Proper hierarchy relationship
    a.approver in a.expense.applicant.^manages or a.approver.role = FinanceDirector
}

// Predicate: System invariants hold
pred systemInvariants {
    // All expenses have valid amounts
    all e: Expense | e.amount > 0 and e.amount <= 10000000
    
    // No circular management relationships
    no u: User | u in u.^manages
    
    // All approvals are valid
    all a: Approval | validApprovalAction[a]
    
    // Status consistency maintained
    all e: Expense | {
        e.status = Approved implies 
            (e.amount <= 10000 and one a: e.~expense | a.approver.role = Manager) or
            (e.amount > 10000 and e.amount <= 50000 and 
             one a1: e.~expense | a1.approver.role = Manager and
             one a2: e.~expense | a2.approver.role = Director) or
            (e.amount > 50000 and
             one a1: e.~expense | a1.approver.role = Manager and
             one a2: e.~expense | a2.approver.role = Director and
             one a3: e.~expense | a3.approver.role = FinanceDirector)
    }
}

// ====================== ASSERTIONS ======================

// Assert: No user can approve their own expense
assert NoSelfApprovalAssertion {
    all a: Approval | a.approver != a.expense.applicant
}

// Assert: Approval hierarchy is respected
assert ApprovalHierarchyAssertion {
    all e: Expense | e.status = Approved implies {
        let approvals = e.~expense |
        all a: approvals | validApprovalAction[a]
    }
}

// Assert: Amount-based approval rules are enforced
assert AmountBasedRulesAssertion {
    all e: Expense | e.status = Approved implies {
        // Low amount: only manager needed
        (e.amount <= 10000 implies 
            one a: e.~expense | a.approver.role = Manager and a.action = Approve) and
        
        // Medium amount: manager + director needed
        (e.amount > 10000 and e.amount <= 50000 implies 
            one a: e.~expense | a.approver.role = Manager and a.action = Approve and
            one a: e.~expense | a.approver.role = Director and a.action = Approve) and
            
        // High amount: manager + director + finance director needed  
        (e.amount > 50000 implies
            one a: e.~expense | a.approver.role = Manager and a.action = Approve and
            one a: e.~expense | a.approver.role = Director and a.action = Approve and
            one a: e.~expense | a.approver.role = FinanceDirector and a.action = Approve)
    }
}

// Check assertions
check NoSelfApprovalAssertion for 5
check ApprovalHierarchyAssertion for 5  
check AmountBasedRulesAssertion for 5

// Run predicate to find valid examples
run systemInvariants for 5

// Run to find counterexamples (should find none if model is correct)
run {
    some e: Expense | e.status = Approved
    some a: Approval | a.approver = a.expense.applicant
} for 5
