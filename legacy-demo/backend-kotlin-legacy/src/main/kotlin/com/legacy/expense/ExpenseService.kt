package com.legacy.expense

import org.springframework.stereotype.Service
import java.time.LocalDateTime

// Problem: Service with mutable state and side effects
@Service
class ExpenseService(
    private val expenseRepository: ExpenseRepository,
    private val userRepository: UserRepository,
    private val approvalHistoryRepository: ApprovalHistoryRepository
) {
    
    // Problem: Mutable cache without proper invalidation
    private var cachedUsers: List<UserEntity> = emptyList()
    private var lastCacheUpdate: LocalDateTime? = null
    
    // Problem: No input validation
    fun createExpense(applicant: String, amount: Double, type: String, description: String): ExpenseEntity {
        val expense = ExpenseEntity(
            applicant = applicant,
            amount = amount, // Problem: No validation for negative amounts
            type = type,
            description = description,
            status = "draft"
        )
        
        // Problem: No validation before save
        return expenseRepository.save(expense)
    }
    
    // Problem: No authorization check
    fun submitExpense(expenseId: Long): ExpenseEntity? {
        val expense = expenseRepository.findById(expenseId).orElse(null)
            ?: return null // Problem: Silent failure
        
        // Problem: Direct mutation
        expense.submit()
        
        // Problem: No validation of business rules
        return expenseRepository.save(expense)
    }
    
    // Problem: Complex business logic with multiple side effects
    fun approveExpense(expenseId: Long, approverId: String, comment: String): Boolean {
        val expense = expenseRepository.findById(expenseId).orElse(null)
            ?: return false // Problem: Silent failure
        
        val approver = getUserByEmail(approverId) // Problem: Using email as ID
            ?: return false
        
        // Problem: No proper authorization check
        if (!canApprove(approverId, expenseId)) {
            return false
        }
        
        // Problem: Direct string manipulation
        expense.addApproval(approverId, "approve", comment)
        
        // Problem: Complex status update logic
        updateExpenseStatus(expense)
        
        // Problem: Multiple save operations without transaction
        expenseRepository.save(expense)
        
        // Problem: Separate approval history save
        val approvalHistory = ApprovalHistoryEntity(
            expenseId = expenseId,
            approverId = approverId,
            timestamp = LocalDateTime.now(),
            action = "approve",
            comment = comment
        )
        approvalHistoryRepository.save(approvalHistory)
        
        return true
    }
    
    // Problem: No input validation for rejection
    fun rejectExpense(expenseId: Long, approverId: String, comment: String): Boolean {
        val expense = expenseRepository.findById(expenseId).orElse(null)
            ?: return false
        
        // Problem: No authorization check for rejection
        expense.addApproval(approverId, "reject", comment)
        expense.status = "rejected" // Problem: Direct mutation
        
        expenseRepository.save(expense)
        
        val approvalHistory = ApprovalHistoryEntity(
            expenseId = expenseId,
            approverId = approverId,
            timestamp = LocalDateTime.now(),
            action = "reject",
            comment = comment
        )
        approvalHistoryRepository.save(approvalHistory)
        
        return true
    }
    
    // Problem: Complex authorization logic with multiple DB calls
    private fun canApprove(approverId: String, expenseId: Long): Boolean {
        val expense = expenseRepository.findById(expenseId).orElse(null)
            ?: return false
        
        val approver = getUserByEmail(approverId)
            ?: return false
        
        // Problem: Self-approval check is insufficient
        if (expense.applicant == approverId) {
            return false
        }
        
        // Problem: Hard-coded business rules
        return when {
            expense.amount <= 10000 -> {
                approver.role == "manager" && isManagerOf(approverId, expense.applicant)
            }
            expense.amount <= 50000 -> {
                when (approver.role) {
                    "manager" -> isManagerOf(approverId, expense.applicant) && !hasManagerApproval(expense)
                    "director" -> hasManagerApproval(expense) && isDirectorOf(approverId, expense.applicant)
                    else -> false
                }
            }
            else -> {
                when (approver.role) {
                    "manager" -> isManagerOf(approverId, expense.applicant) && !hasManagerApproval(expense)
                    "director" -> hasManagerApproval(expense) && !hasDirectorApproval(expense)
                    "finance_director" -> hasManagerApproval(expense) && hasDirectorApproval(expense)
                    else -> false
                }
            }
        }
    }
    
    // Problem: Inefficient user lookup with caching issues
    private fun getUserByEmail(email: String): UserEntity? {
        if (cachedUsers.isEmpty() || lastCacheUpdate?.isBefore(LocalDateTime.now().minusMinutes(5)) == true) {
            // Problem: Full table scan for cache refresh
            cachedUsers = userRepository.findAll()
            lastCacheUpdate = LocalDateTime.now()
        }
        
        return cachedUsers.find { it.email == email }
    }
    
    // Problem: Complex relationship checking
    private fun isManagerOf(managerId: String, employeeEmail: String): Boolean {
        val manager = getUserByEmail(managerId) ?: return false
        val employee = getUserByEmail(employeeEmail) ?: return false
        
        // Problem: Nullable managerId not handled properly
        return employee.managerId == manager.id
    }
    
    private fun isDirectorOf(directorId: String, employeeEmail: String): Boolean {
        val employee = getUserByEmail(employeeEmail) ?: return false
        val manager = employee.managerId?.let { userRepository.findById(it).orElse(null) }
            ?: return false
        
        val director = getUserByEmail(directorId) ?: return false
        
        return manager.managerId == director.id
    }
    
    // Problem: String parsing for approval checking
    private fun hasManagerApproval(expense: ExpenseEntity): Boolean {
        return expense.getApprovalList().any { approval ->
            val approverEmail = approval["approver"] as String
            val approver = getUserByEmail(approverEmail)
            approver?.role == "manager"
        }
    }
    
    private fun hasDirectorApproval(expense: ExpenseEntity): Boolean {
        return expense.getApprovalList().any { approval ->
            val approverEmail = approval["approver"] as String
            val approver = getUserByEmail(approverEmail)
            approver?.role == "director"
        }
    }
    
    // Problem: Complex status update with side effects
    private fun updateExpenseStatus(expense: ExpenseEntity) {
        val hasManager = hasManagerApproval(expense)
        val hasDirector = hasDirectorApproval(expense)
        val hasFinance = expense.getApprovalList().any { approval ->
            val approverEmail = approval["approver"] as String
            val approver = getUserByEmail(approverEmail)
            approver?.role == "finance_director"
        }
        
        // Problem: Complex nested conditions
        expense.status = when {
            expense.amount <= 10000 -> {
                if (hasManager) "approved" else "manager_review"
            }
            expense.amount <= 50000 -> {
                when {
                    hasManager && hasDirector -> "approved"
                    hasManager -> "director_review"
                    else -> "manager_review"
                }
            }
            else -> {
                when {
                    hasManager && hasDirector && hasFinance -> "approved"
                    hasManager && hasDirector -> "finance_review"
                    hasManager -> "director_review"
                    else -> "manager_review"
                }
            }
        }
    }
    
    // Problem: No error handling for database operations
    fun getExpensesByApplicant(applicant: String): List<ExpenseEntity> {
        return expenseRepository.findByApplicant(applicant)
    }
    
    // Problem: Returning mutable entities
    fun getAllExpenses(): List<ExpenseEntity> {
        return expenseRepository.findAll()
    }
    
    // Problem: No pagination for potentially large results
    fun getPendingExpenses(): List<ExpenseEntity> {
        return expenseRepository.findPendingExpenses()
    }
    
    // Problem: Business logic mixed with data access
    fun getExpensesForApproval(approverId: String): List<ExpenseEntity> {
        return getAllExpenses().filter { expense ->
            canApprove(approverId, expense.id ?: 0) // Problem: Unsafe null handling
        }
    }
    
    // Problem: No input validation
    fun updateExpense(expenseId: Long, amount: Double?, type: String?, description: String?): ExpenseEntity? {
        val expense = expenseRepository.findById(expenseId).orElse(null)
            ?: return null
        
        // Problem: Direct mutation without validation
        amount?.let { expense.amount = it }
        type?.let { expense.type = it }
        description?.let { expense.description = it }
        
        return expenseRepository.save(expense)
    }
    
    // Problem: No soft delete, direct deletion
    fun deleteExpense(expenseId: Long): Boolean {
        return try {
            expenseRepository.deleteById(expenseId)
            true
        } catch (e: Exception) {
            // Problem: Silent error handling
            false
        }
    }
}