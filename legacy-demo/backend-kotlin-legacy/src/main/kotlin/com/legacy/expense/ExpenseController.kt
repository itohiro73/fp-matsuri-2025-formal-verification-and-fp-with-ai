package com.legacy.expense

import org.springframework.http.ResponseEntity
import org.springframework.web.bind.annotation.*

// Problem: Controller with business logic and poor error handling
@RestController
@RequestMapping("/api/expenses")
class ExpenseController(private val expenseService: ExpenseService) {
    
    // Problem: No input validation annotations
    @PostMapping
    fun createExpense(@RequestBody request: Map<String, Any>): ResponseEntity<Any> {
        try {
            // Problem: Unsafe casting without validation
            val applicant = request["applicant"] as String
            val amount = (request["amount"] as Number).toDouble() // Problem: Potential ClassCastException
            val type = request["type"] as String
            val description = request["description"] as? String ?: ""
            
            // Problem: No business rule validation
            val expense = expenseService.createExpense(applicant, amount, type, description)
            
            // Problem: Returning entity directly (no DTO)
            return ResponseEntity.ok(expense)
        } catch (e: ClassCastException) {
            // Problem: Generic error response
            return ResponseEntity.badRequest().body("Invalid request format")
        } catch (e: Exception) {
            // Problem: Exposing internal errors
            return ResponseEntity.internalServerError().body("Error: ${e.message}")
        }
    }
    
    // Problem: No path variable validation
    @PostMapping("/{id}/submit")
    fun submitExpense(@PathVariable id: Long): ResponseEntity<Any> {
        val expense = expenseService.submitExpense(id)
        
        // Problem: Null handling with generic message
        return if (expense != null) {
            ResponseEntity.ok(expense)
        } else {
            ResponseEntity.notFound().build()
        }
    }
    
    // Problem: Complex request body without proper DTO
    @PostMapping("/{id}/approve")
    fun approveExpense(
        @PathVariable id: Long,
        @RequestBody request: Map<String, String>
    ): ResponseEntity<String> {
        val approverId = request["approverId"] ?: return ResponseEntity.badRequest().body("Missing approverId")
        val comment = request["comment"] ?: ""
        
        // Problem: Boolean return converted to string
        val result = expenseService.approveExpense(id, approverId, comment)
        
        return if (result) {
            ResponseEntity.ok("Expense approved successfully")
        } else {
            // Problem: Generic failure message
            ResponseEntity.badRequest().body("Failed to approve expense")
        }
    }
    
    @PostMapping("/{id}/reject")
    fun rejectExpense(
        @PathVariable id: Long,
        @RequestBody request: Map<String, String>
    ): ResponseEntity<String> {
        val approverId = request["approverId"] ?: return ResponseEntity.badRequest().body("Missing approverId")
        val comment = request["comment"] ?: ""
        
        val result = expenseService.rejectExpense(id, approverId, comment)
        
        return if (result) {
            ResponseEntity.ok("Expense rejected successfully")
        } else {
            ResponseEntity.badRequest().body("Failed to reject expense")
        }
    }
    
    // Problem: No pagination for potentially large lists
    @GetMapping
    fun getAllExpenses(): ResponseEntity<List<ExpenseEntity>> {
        val expenses = expenseService.getAllExpenses()
        return ResponseEntity.ok(expenses)
    }
    
    // Problem: No input validation for query parameter
    @GetMapping("/by-applicant")
    fun getExpensesByApplicant(@RequestParam applicant: String): ResponseEntity<List<ExpenseEntity>> {
        // Problem: No validation that applicant exists
        val expenses = expenseService.getExpensesByApplicant(applicant)
        return ResponseEntity.ok(expenses)
    }
    
    @GetMapping("/pending")
    fun getPendingExpenses(): ResponseEntity<List<ExpenseEntity>> {
        val expenses = expenseService.getPendingExpenses()
        return ResponseEntity.ok(expenses)
    }
    
    // Problem: Business logic in controller
    @GetMapping("/for-approval")
    fun getExpensesForApproval(@RequestParam approverId: String): ResponseEntity<List<ExpenseEntity>> {
        // Problem: No validation that approverId is valid user
        val expenses = expenseService.getExpensesForApproval(approverId)
        return ResponseEntity.ok(expenses)
    }
    
    @GetMapping("/{id}")
    fun getExpenseById(@PathVariable id: Long): ResponseEntity<ExpenseEntity> {
        return try {
            // Problem: Direct database access without service abstraction
            val expense = expenseService.getAllExpenses().find { it.id == id }
            if (expense != null) {
                ResponseEntity.ok(expense)
            } else {
                ResponseEntity.notFound().build()
            }
        } catch (e: Exception) {
            ResponseEntity.internalServerError().build()
        }
    }
    
    // Problem: Partial update without proper validation
    @PutMapping("/{id}")
    fun updateExpense(
        @PathVariable id: Long,
        @RequestBody request: Map<String, Any>
    ): ResponseEntity<Any> {
        try {
            val amount = request["amount"]?.let { (it as Number).toDouble() }
            val type = request["type"] as? String
            val description = request["description"] as? String
            
            // Problem: No validation of update rules (e.g., can't update approved expense)
            val expense = expenseService.updateExpense(id, amount, type, description)
            
            return if (expense != null) {
                ResponseEntity.ok(expense)
            } else {
                ResponseEntity.notFound().build()
            }
        } catch (e: Exception) {
            return ResponseEntity.badRequest().body("Invalid update data")
        }
    }
    
    // Problem: No authorization check for deletion
    @DeleteMapping("/{id}")
    fun deleteExpense(@PathVariable id: Long): ResponseEntity<String> {
        val result = expenseService.deleteExpense(id)
        
        return if (result) {
            ResponseEntity.ok("Expense deleted successfully")
        } else {
            ResponseEntity.badRequest().body("Failed to delete expense")
        }
    }
    
    // Problem: Complex aggregation logic in controller
    @GetMapping("/stats")
    fun getExpenseStats(): ResponseEntity<Map<String, Any>> {
        val allExpenses = expenseService.getAllExpenses()
        
        // Problem: In-memory processing of all data
        val stats = mapOf(
            "total" to allExpenses.size,
            "approved" to allExpenses.count { it.status == "approved" },
            "pending" to allExpenses.count { it.status != "approved" && it.status != "rejected" },
            "rejected" to allExpenses.count { it.status == "rejected" },
            "totalAmount" to allExpenses.filter { it.status == "approved" }.sumOf { it.amount }
        )
        
        return ResponseEntity.ok(stats)
    }
}

// Problem: Separate controller without proper organization
@RestController
@RequestMapping("/api/users")
class UserController(private val expenseService: ExpenseService) {
    
    // Problem: Business logic in controller
    @GetMapping("/{email}/pending-approvals")
    fun getPendingApprovals(@PathVariable email: String): ResponseEntity<List<ExpenseEntity>> {
        // Problem: Using email as identifier in URL
        val expenses = expenseService.getExpensesForApproval(email)
        return ResponseEntity.ok(expenses)
    }
    
    // Problem: No proper user management service
    @GetMapping("/{email}/expenses")
    fun getUserExpenses(@PathVariable email: String): ResponseEntity<List<ExpenseEntity>> {
        val expenses = expenseService.getExpensesByApplicant(email)
        return ResponseEntity.ok(expenses)
    }
}