package com.bookstore.domain

import arrow.core.Either
import arrow.core.left
import arrow.core.right
import kotlinx.serialization.Serializable

/**
 * Immutable domain entities derived from formal specifications
 * These entities enforce business invariants at the type level
 */

// === Domain Errors ===

sealed interface DomainError {
    val message: String
    
    data class InsufficientStock(override val message: String = "Insufficient stock available") : DomainError
    data class InvalidStateTransition(override val message: String) : DomainError
    data class PaymentRequired(override val message: String = "Payment must be completed before shipping") : DomainError
    data class ReservationExpired(override val message: String = "Reservation has expired") : DomainError
    data class OrderNotCancellable(override val message: String = "Order cannot be cancelled in current state") : DomainError
    data class ConcurrentProcessing(override val message: String = "Another order for this book is being processed") : DomainError
}

// === Book Entity ===

/**
 * Immutable book entity
 */
@Serializable
data class Book(
    val id: BookId,
    val isbn: ISBN,
    val title: String,
    val price: Money
) {
    init {
        require(title.isNotBlank()) { "Book title cannot be blank" }
    }
}

// === Customer Entity ===

/**
 * Immutable customer entity
 */
@Serializable
data class Customer(
    val id: CustomerId,
    val name: String,
    val email: String
) {
    init {
        require(name.isNotBlank()) { "Customer name cannot be blank" }
        require(email.contains("@")) { "Invalid email format" }
    }
}

// === Order Entity ===

/**
 * Immutable order entity with type-safe state transitions
 * RESOLVED AMBIGUITY: All state transition rules from formal verification
 */
@Serializable
data class Order(
    val id: OrderId,
    val customerId: CustomerId,
    val bookId: BookId,
    val quantity: Quantity,
    val status: OrderStatus,
    val paymentStatus: PaymentStatus,
    val reservationStatus: ReservationStatus,
    val createdAt: Timestamp,
    val updatedAt: Timestamp
) {
    
    /**
     * Confirm a reserved order (Reserved -> Confirmed)
     * RESOLVED AMBIGUITY: Mutual exclusion for order processing
     */
    fun confirm(): Either<DomainError, Order> =
        when (status) {
            OrderStatus.Reserved -> copy(
                status = OrderStatus.Confirmed,
                updatedAt = Timestamp.now()
            ).right()
            else -> DomainError.InvalidStateTransition(
                "Cannot confirm order in status: $status"
            ).left()
        }
    
    /**
     * Ship a confirmed order (Confirmed -> Shipped)
     * RESOLVED AMBIGUITY: Payment must be completed before shipping
     */
    fun ship(): Either<DomainError, Order> =
        when {
            status != OrderStatus.Confirmed -> DomainError.InvalidStateTransition(
                "Cannot ship order in status: $status"
            ).left()
            paymentStatus != PaymentStatus.Completed -> DomainError.PaymentRequired().left()
            else -> copy(
                status = OrderStatus.Shipped,
                updatedAt = Timestamp.now()
            ).right()
        }
    
    /**
     * Cancel an order (Reserved -> Cancelled)
     * RESOLVED AMBIGUITY: Only reserved orders can be cancelled
     */
    fun cancel(): Either<DomainError, Order> =
        when (status) {
            OrderStatus.Reserved -> copy(
                status = OrderStatus.Cancelled,
                reservationStatus = ReservationStatus.Released,
                updatedAt = Timestamp.now()
            ).right()
            else -> DomainError.OrderNotCancellable(
                "Cannot cancel order in status: $status"
            ).left()
        }
    
    /**
     * Complete payment (Pending -> Completed)
     */
    fun completePayment(): Either<DomainError, Order> =
        when (paymentStatus) {
            PaymentStatus.Pending -> copy(
                paymentStatus = PaymentStatus.Completed,
                updatedAt = Timestamp.now()
            ).right()
            else -> DomainError.InvalidStateTransition(
                "Payment already in status: $paymentStatus"
            ).left()
        }
    
    /**
     * Fail payment (Pending -> Failed)
     * This will trigger automatic cancellation
     */
    fun failPayment(): Either<DomainError, Order> =
        when (paymentStatus) {
            PaymentStatus.Pending -> copy(
                paymentStatus = PaymentStatus.Failed,
                status = OrderStatus.Cancelled,
                reservationStatus = ReservationStatus.Released,
                updatedAt = Timestamp.now()
            ).right()
            else -> DomainError.InvalidStateTransition(
                "Payment already in status: $paymentStatus"
            ).left()
        }
    
    /**
     * Expire reservation (Active -> Expired)
     * RESOLVED AMBIGUITY: Automatic timeout handling
     */
    fun expireReservation(timeout: ReservationTimeout): Either<DomainError, Order> =
        when {
            status != OrderStatus.Reserved -> DomainError.InvalidStateTransition(
                "Cannot expire reservation for order in status: $status"
            ).left()
            !timeout.isExpired(createdAt, Timestamp.now()) -> DomainError.InvalidStateTransition(
                "Reservation has not yet expired"
            ).left()
            else -> copy(
                status = OrderStatus.Cancelled,
                reservationStatus = ReservationStatus.Expired(Timestamp.now().epochMilli),
                updatedAt = Timestamp.now()
            ).right()
        }
    
    /**
     * Check if order can be processed (for mutual exclusion)
     */
    fun canBeProcessed(): Boolean = status == OrderStatus.Reserved
    
    /**
     * Check if order is active (has reserved inventory)
     */
    fun hasActiveReservation(): Boolean = 
        status in setOf(OrderStatus.Reserved, OrderStatus.Confirmed, OrderStatus.Shipped) &&
        reservationStatus == ReservationStatus.Active
    
    companion object {
        /**
         * Create a new order with atomic inventory reservation
         * RESOLVED AMBIGUITY: Atomic inventory check and reservation at order placement
         */
        fun create(
            customerId: CustomerId,
            bookId: BookId,
            quantity: Quantity
        ): Order = Order(
            id = OrderId.generate(),
            customerId = customerId,
            bookId = bookId,
            quantity = quantity,
            status = OrderStatus.Reserved,
            paymentStatus = PaymentStatus.Pending,
            reservationStatus = ReservationStatus.Active,
            createdAt = Timestamp.now(),
            updatedAt = Timestamp.now()
        )
    }
}

// === Aggregate Root: BookInventory ===

/**
 * Aggregate root that manages book inventory and orders
 * Enforces all invariants from formal verification
 */
@Serializable
data class BookInventory(
    val book: Book,
    val inventory: Inventory,
    val processingOrderId: OrderId? = null // For mutual exclusion
) {
    
    /**
     * Place an order with atomic inventory reservation
     * RESOLVED AMBIGUITY: Atomic inventory check and reservation
     */
    fun placeOrder(
        customerId: CustomerId,
        quantity: Quantity
    ): Either<DomainError, Pair<BookInventory, Order>> =
        inventory.reserve(quantity).fold(
            ifEmpty = { DomainError.InsufficientStock().left() },
            ifSome = { newInventory ->
                val order = Order.create(customerId, book.id, quantity)
                val updatedBookInventory = copy(inventory = newInventory)
                (updatedBookInventory to order).right()
            }
        )
    
    /**
     * Start processing an order (for mutual exclusion)
     * RESOLVED AMBIGUITY: Mutual exclusion for order processing
     */
    fun startProcessing(orderId: OrderId): Either<DomainError, BookInventory> =
        when (processingOrderId) {
            null -> copy(processingOrderId = orderId).right()
            else -> DomainError.ConcurrentProcessing().left()
        }
    
    /**
     * Finish processing an order
     */
    fun finishProcessing(): BookInventory = copy(processingOrderId = null)
    
    /**
     * Cancel an order and restore inventory
     * RESOLVED AMBIGUITY: Immediate inventory restoration
     */
    fun cancelOrder(order: Order): Either<DomainError, Pair<BookInventory, Order>> =
        order.cancel().map { cancelledOrder ->
            val restoredInventory = inventory.release(order.quantity)
            val updatedBookInventory = copy(
                inventory = restoredInventory,
                processingOrderId = if (processingOrderId == order.id) null else processingOrderId
            )
            updatedBookInventory to cancelledOrder
        }
    
    /**
     * Handle payment failure (automatic cancellation with inventory restoration)
     */
    fun handlePaymentFailure(order: Order): Either<DomainError, Pair<BookInventory, Order>> =
        order.failPayment().map { failedOrder ->
            val restoredInventory = inventory.release(order.quantity)
            val updatedBookInventory = copy(
                inventory = restoredInventory,
                processingOrderId = if (processingOrderId == order.id) null else processingOrderId
            )
            updatedBookInventory to failedOrder
        }
    
    /**
     * Handle reservation timeout
     * RESOLVED AMBIGUITY: Automatic timeout handling
     */
    fun handleTimeout(
        order: Order, 
        timeout: ReservationTimeout
    ): Either<DomainError, Pair<BookInventory, Order>> =
        order.expireReservation(timeout).map { expiredOrder ->
            val restoredInventory = inventory.release(order.quantity)
            val updatedBookInventory = copy(
                inventory = restoredInventory,
                processingOrderId = if (processingOrderId == order.id) null else processingOrderId
            )
            updatedBookInventory to expiredOrder
        }
    
    companion object {
        fun create(book: Book, totalStock: Stock): BookInventory = BookInventory(
            book = book,
            inventory = Inventory.initial(totalStock)
        )
    }
} 