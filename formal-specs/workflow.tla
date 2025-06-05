---- MODULE workflow ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS
    Users,          \* Set of all users
    MaxAmount,      \* Maximum expense amount
    Expenses,       \* Set of all expense IDs
    NoManager       \* Special value for users without managers

VARIABLES
    expenses,       \* Function from expense ID to expense record
    approvals,      \* Function from expense ID to sequence of approvals
    users          \* Function from user ID to user record

TypeOK ==
    /\ expenses \in [Expenses -> 
        [applicant: Users, 
         amount: 1..MaxAmount, 
         type: {"travel", "accommodation", "meeting", "equipment"},
         description: {"", "business_trip", "client_meeting", "equipment_purchase", "other"},
         status: {"draft", "submitted", "manager_review", "director_review", "finance_review", "approved", "rejected"},
         submit_time: Nat]]
    /\ approvals \in [Expenses -> Seq([approver: Users, timestamp: Nat, action: {"approve", "reject"}, comment: {"", "approved", "rejected", "needs_revision"}])]
    /\ users \in [Users -> [name: {"user1", "user2", "user3", "user4", "user5"}, email: {"email1", "email2", "email3", "email4", "email5"}, role: {"employee", "manager", "director", "finance_director"}, manager: Users \cup {NoManager}]]

\* Define approval path based on amount
ApprovalPath(amount) ==
    IF amount <= 10000 THEN <<"manager">>
    ELSE IF amount <= 50000 THEN <<"manager", "director">>
    ELSE <<"manager", "director", "finance_director">>

\* Get next required approver role
NextApproverRole(expense_id) ==
    LET expense == expenses[expense_id]
        approval_seq == approvals[expense_id]
        required_path == ApprovalPath(expense.amount)
        current_position == Len(approval_seq) + 1
    IN IF current_position <= Len(required_path)
       THEN required_path[current_position]
       ELSE "none"

\* Check if user has required role
HasRole(user_id, role) ==
    users[user_id].role = role

\* Check if user is manager of applicant
IsManagerOf(manager_id, employee_id) ==
    users[employee_id].manager = manager_id

\* Check if user can approve expense
CanApprove(user_id, expense_id) ==
    LET expense == expenses[expense_id]
        required_role == NextApproverRole(expense_id)
    IN /\ user_id # expense.applicant  \* Cannot self-approve
       /\ required_role # "none"        \* More approvals needed
       /\ CASE required_role = "manager" -> 
                /\ HasRole(user_id, "manager") 
                /\ IsManagerOf(user_id, expense.applicant)
            [] required_role = "director" ->
                /\ HasRole(user_id, "director")
                \* Director must be manager of the expense applicant's manager
                /\ \E manager \in Users : 
                    /\ HasRole(manager, "manager")
                    /\ IsManagerOf(manager, expense.applicant)
                    /\ IsManagerOf(user_id, manager)
            [] required_role = "finance_director" ->
                HasRole(user_id, "finance_director")
            [] OTHER -> FALSE

\* Initial state
Init ==
    /\ expenses = [e \in Expenses |-> 
        [applicant |-> CHOOSE u \in Users : TRUE,
         amount |-> 1,
         type |-> "travel",
         description |-> "",
         status |-> "draft",
         submit_time |-> 0]]
    /\ approvals = [e \in Expenses |-> <<>>]
    /\ users \in [Users -> [name: {"user1", "user2", "user3", "user4", "user5"}, email: {"email1", "email2", "email3", "email4", "email5"}, role: {"employee", "manager", "director", "finance_director"}, manager: Users \cup {NoManager}]]

\* Submit expense application
SubmitExpense(expense_id, applicant, amount, expense_type, description) ==
    /\ expenses[expense_id].status = "draft"
    /\ expenses' = [expenses EXCEPT ![expense_id] = 
        [applicant |-> applicant,
         amount |-> amount,
         type |-> expense_type,
         description |-> description,
         status |-> "submitted",
         submit_time |-> expenses[expense_id].submit_time + 1]]
    /\ UNCHANGED <<approvals, users>>

\* Approve or reject expense
ProcessApproval(user_id, expense_id, action, comment) ==
    /\ CanApprove(user_id, expense_id)
    /\ expenses[expense_id].status \in {"submitted", "manager_review", "director_review", "finance_review"}
    /\ LET new_approval == [approver |-> user_id, 
                           timestamp |-> expenses[expense_id].submit_time + Len(approvals[expense_id]) + 1,
                           action |-> action,
                           comment |-> comment]
           updated_approvals == Append(approvals[expense_id], new_approval)
           required_path == ApprovalPath(expenses[expense_id].amount)
       IN /\ approvals' = [approvals EXCEPT ![expense_id] = updated_approvals]
          /\ IF action = "reject"
             THEN expenses' = [expenses EXCEPT ![expense_id].status = "rejected"]
             ELSE IF Len(updated_approvals) = Len(required_path)
                  THEN expenses' = [expenses EXCEPT ![expense_id].status = "approved"]
                  ELSE expenses' = [expenses EXCEPT ![expense_id].status = 
                        CASE NextApproverRole(expense_id) = "manager" -> "manager_review"
                          [] NextApproverRole(expense_id) = "director" -> "director_review"
                          [] NextApproverRole(expense_id) = "finance_director" -> "finance_review"
                          [] OTHER -> "approved"]
    /\ UNCHANGED users

\* Auto-escalation after 72 hours (simplified as step counter)
AutoEscalate(expense_id) ==
    /\ expenses[expense_id].status \in {"submitted", "manager_review", "director_review", "finance_review"}
    /\ expenses[expense_id].submit_time + Len(approvals[expense_id]) > 3  \* Simulate 72 hours
    /\ LET next_role == NextApproverRole(expense_id)
       IN \E escalated_approver \in Users :
            /\ HasRole(escalated_approver, next_role)
            /\ CanApprove(escalated_approver, expense_id)
            /\ ProcessApproval(escalated_approver, expense_id, "approve", "Auto-escalated")

\* Deadline check (2 weeks = 14 steps)
DeadlineExpired(expense_id) ==
    /\ expenses[expense_id].status \in {"submitted", "manager_review", "director_review", "finance_review"}
    /\ expenses[expense_id].submit_time + Len(approvals[expense_id]) > 14
    /\ expenses' = [expenses EXCEPT ![expense_id].status = "rejected"]
    /\ UNCHANGED <<approvals, users>>

\* Next state relation
Next ==
    \/ \E expense_id \in Expenses, applicant \in Users, amount \in 1..MaxAmount, 
         expense_type \in {"travel", "accommodation", "meeting", "equipment"}, description \in {"", "business_trip", "client_meeting", "equipment_purchase", "other"} :
         SubmitExpense(expense_id, applicant, amount, expense_type, description)
    \/ \E user_id \in Users, expense_id \in Expenses, action \in {"approve", "reject"}, comment \in {"", "approved", "rejected", "needs_revision"} :
         ProcessApproval(user_id, expense_id, action, comment)
    \/ \E expense_id \in Expenses : AutoEscalate(expense_id)
    \/ \E expense_id \in Expenses : DeadlineExpired(expense_id)

\* Specification
Spec == Init /\ [][Next]_<<expenses, approvals, users>>

\* Safety properties
NoSelfApproval == \A expense_id \in Expenses :
    LET expense == expenses[expense_id]
        approval_seq == approvals[expense_id]
    IN \A i \in 1..Len(approval_seq) :
        approval_seq[i].approver # expense.applicant

SequentialApproval == \A expense_id \in Expenses :
    LET expense == expenses[expense_id]
        approval_seq == approvals[expense_id]
        required_path == ApprovalPath(expense.amount)
    IN \A i \in 1..Len(approval_seq) :
        HasRole(approval_seq[i].approver, required_path[i])

OnlyAuthorizedApprovers == \A expense_id \in Expenses :
    LET expense == expenses[expense_id]
        approval_seq == approvals[expense_id]
    IN \A i \in 1..Len(approval_seq) :
        LET approver == approval_seq[i].approver
            required_role == ApprovalPath(expense.amount)[i]
        IN CASE required_role = "manager" -> IsManagerOf(approver, expense.applicant)
            [] required_role = "director" -> 
                \E manager \in Users : 
                    /\ HasRole(manager, "manager")
                    /\ IsManagerOf(manager, expense.applicant)
                    /\ IsManagerOf(approver, manager)
            [] required_role = "finance_director" -> HasRole(approver, "finance_director")
            [] OTHER -> FALSE

\* Liveness properties
ExpenseEventuallyProcessed == \A expense_id \in Expenses :
    expenses[expense_id].status = "submitted" ~> 
    expenses[expense_id].status \in {"approved", "rejected"}

====