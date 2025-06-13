package com.legacy.expense

import org.springframework.boot.autoconfigure.SpringBootApplication
import org.springframework.boot.runApplication

@SpringBootApplication
class ExpenseApplication

fun main(args: Array<String>) {
    runApplication<ExpenseApplication>(*args)
}

// AIが生成した危険なコード
fun processOrder(bookId: String, quantity: Int, customerId: String): Boolean {
    val book = bookRepository.findById(bookId)
    if (book != null && book.stock >= quantity) {
        book.stock -= quantity  // 🚨 同時注文時の競合状態
        orderRepository.save(Order(customerId, bookId, quantity))
        return true
    }
    return false
}