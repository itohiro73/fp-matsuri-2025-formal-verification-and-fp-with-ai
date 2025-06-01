package com.legacy.expense

import jakarta.persistence.*
import java.time.LocalDateTime

// Problem: Mutable entity with public setters
@Entity
@Table(name = "expenses")
data class ExpenseEntity(
    @Id
    @GeneratedValue(strategy = GenerationType.IDENTITY)
    var id: Long? = null, // Problem: Nullable ID can cause issues
    
    var applicant: String = "", // Problem: No validation, can be empty
    var amount: Double = 0.0, // Problem: Can be negative, using Double for money
    var type: String = "", // Problem: Should be enum
    var description: String = "",
    var status: String = "draft", // Problem: Should be enum
    var submitTime: LocalDateTime? = null, // Problem: Nullable time
    
    // Problem: Storing approvals as comma-separated string
    @Column(columnDefinition = "TEXT")
    var approvals: String = "" // Problem: No type safety, parsing issues
) {
    // Problem: Business logic in entity
    fun isEditable(): Boolean {
        return status == "draft" || status == "rejected"
    }
    
    // Problem: Mutable state change method in entity
    fun submit() {
        this.status = "submitted"
        this.submitTime = LocalDateTime.now()
    }
    
    // Problem: Complex business logic in entity
    fun getRequiredApprovers(): List<String> {
        return when {
            amount <= 10000 -> listOf("manager")
            amount <= 50000 -> listOf("manager", "director")
            else -> listOf("manager", "director", "finance_director")
        }
    }
    
    // Problem: String parsing logic in entity
    fun getApprovalList(): List<Map<String, Any>> {
        if (approvals.isEmpty()) return emptyList()
        
        return try {
            approvals.split(";").map { approval ->
                val parts = approval.split("|")
                mapOf(
                    "approver" to parts[0],
                    "timestamp" to parts[1],
                    "action" to parts[2],
                    "comment" to (parts.getOrNull(3) ?: "")
                )
            }
        } catch (e: Exception) {
            // Problem: Silent error handling
            emptyList()
        }
    }
    
    // Problem: Direct string manipulation for data
    fun addApproval(approver: String, action: String, comment: String) {
        val timestamp = System.currentTimeMillis().toString()
        val approval = "$approver|$timestamp|$action|$comment"
        
        if (approvals.isEmpty()) {
            approvals = approval
        } else {
            approvals += ";$approval"
        }
    }
    
    // Problem: Business logic mixed with data access
    fun canBeApprovedBy(userId: String): Boolean {
        // Problem: No actual validation logic
        return userId != applicant
    }
}

// Problem: Mutable user entity
@Entity
@Table(name = "users")
data class UserEntity(
    @Id
    @GeneratedValue(strategy = GenerationType.IDENTITY)
    var id: Long? = null,
    
    var name: String = "",
    var email: String = "",
    var role: String = "", // Problem: Should be enum
    var managerId: Long? = null // Problem: No referential integrity
) {
    // Problem: Business logic in entity
    fun isManagerOf(employeeId: Long): Boolean {
        // Problem: No actual checking logic implemented
        return true // Problem: Always returns true
    }
    
    fun canApprove(amount: Double): Boolean {
        return when (role) {
            "manager" -> amount <= 50000
            "director" -> amount <= 1000000
            "finance_director" -> true
            else -> false
        }
    }
}

// Problem: No separate approval entity
@Entity
@Table(name = "approval_history")
data class ApprovalHistoryEntity(
    @Id
    @GeneratedValue(strategy = GenerationType.IDENTITY)
    var id: Long? = null,
    
    var expenseId: Long = 0, // Problem: No foreign key constraint
    var approverId: String = "",
    var timestamp: LocalDateTime = LocalDateTime.now(),
    var action: String = "", // Problem: Should be enum
    var comment: String = ""
)