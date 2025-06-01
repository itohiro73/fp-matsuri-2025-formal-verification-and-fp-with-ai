package com.legacy.expense

import org.springframework.data.jpa.repository.JpaRepository
import org.springframework.data.jpa.repository.Query
import org.springframework.stereotype.Repository

// Problem: Exposing entity directly from repository
@Repository
interface ExpenseRepository : JpaRepository<ExpenseEntity, Long> {
    
    // Problem: No validation for applicant parameter
    fun findByApplicant(applicant: String): List<ExpenseEntity>
    
    // Problem: String-based status filtering
    fun findByStatus(status: String): List<ExpenseEntity>
    
    // Problem: Complex query in repository
    @Query("SELECT e FROM ExpenseEntity e WHERE e.status = 'submitted' OR e.status = 'manager_review' OR e.status = 'director_review' OR e.status = 'finance_review'")
    fun findPendingExpenses(): List<ExpenseEntity>
    
    // Problem: No pagination for potentially large results
    @Query("SELECT e FROM ExpenseEntity e WHERE e.amount > ?1")
    fun findByAmountGreaterThan(amount: Double): List<ExpenseEntity>
    
    // Problem: Native query that could break with schema changes
    @Query(value = "SELECT * FROM expenses WHERE applicant = ?1 AND status != 'draft'", nativeQuery = true)
    fun findSubmittedExpensesByApplicant(applicant: String): List<ExpenseEntity>
}

@Repository
interface UserRepository : JpaRepository<UserEntity, Long> {
    
    // Problem: No unique constraint handling
    fun findByEmail(email: String): UserEntity?
    
    // Problem: String-based role filtering
    fun findByRole(role: String): List<UserEntity>
    
    // Problem: No validation for managerId
    fun findByManagerId(managerId: Long): List<UserEntity>
    
    // Problem: Complex business logic in repository
    @Query("SELECT u FROM UserEntity u WHERE u.role = 'manager' AND u.id IN (SELECT DISTINCT e.applicant FROM ExpenseEntity e WHERE e.status = 'manager_review')")
    fun findManagersWithPendingApprovals(): List<UserEntity>
}

@Repository
interface ApprovalHistoryRepository : JpaRepository<ApprovalHistoryEntity, Long> {
    
    // Problem: No foreign key validation
    fun findByExpenseId(expenseId: Long): List<ApprovalHistoryEntity>
    
    // Problem: String-based action filtering
    fun findByAction(action: String): List<ApprovalHistoryEntity>
    
    // Problem: No ordering specified for time-sensitive data
    fun findByApproverId(approverId: String): List<ApprovalHistoryEntity>
}