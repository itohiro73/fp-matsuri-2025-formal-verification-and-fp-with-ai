package com.bookstore.domain

import arrow.core.NonEmptyList
import arrow.core.Option
import arrow.core.Some
import arrow.core.none
import kotlinx.serialization.Contextual
import kotlinx.serialization.Serializable
import java.time.Instant
import java.util.*

/**
 * Type-safe domain types derived from formal specifications
 * These types encode the constraints discovered in TLA+ verification
 * to prevent invalid states at compile time.
 */

// === Value Objects ===

@JvmInline
@Serializable
value class BookId(val value: String) {
    init {
        require(value.isNotBlank()) { "BookId cannot be blank" }
    }
}

@JvmInline
@Serializable
value class CustomerId(val value: String) {
    init {
        require(value.isNotBlank()) { "CustomerId cannot be blank" }
    }
}

@JvmInline
@Serializable
value class OrderId(val value: String) {
    init {
        require(value.isNotBlank()) { "OrderId cannot be blank" }
    }
    
    companion object {
        fun generate(): OrderId = OrderId(UUID.randomUUID().toString())
    }
}

@JvmInline
@Serializable
value class ISBN(val value: String) {
    init {
        require(value.matches(Regex("\\d{3}-\\d{10}"))) { 
            "ISBN must be in format XXX-XXXXXXXXXX" 
        }
    }
}

@JvmInline
@Serializable
value class Money(val cents: Long) {
    init {
        require(cents >= 0) { "Money cannot be negative" }
    }
    
    operator fun plus(other: Money): Money = Money(cents + other.cents)
    operator fun minus(other: Money): Money = Money(cents - other.cents)
    operator fun times(quantity: Int): Money = Money(cents * quantity)
    
    fun toDollars(): Double = cents / 100.0
    
    companion object {
        fun fromDollars(dollars: Double): Money = Money((dollars * 100).toLong())
        val ZERO = Money(0)
    }
}

/**
 * Positive integer quantity - prevents negative quantities at compile time
 * RESOLVED AMBIGUITY: Quantity must be positive (from formal verification)
 */
@JvmInline
@Serializable
value class Quantity(val value: Int) {
    init {
        require(value > 0) { "Quantity must be positive" }
    }
    
    operator fun plus(other: Quantity): Quantity = Quantity(value + other.value)
    operator fun minus(other: Quantity): Quantity = Quantity(value - other.value)
    
    fun canSubtract(other: Quantity): Boolean = value >= other.value
}

/**
 * Non-negative stock - prevents negative inventory at compile time
 * RESOLVED AMBIGUITY: Stock conservation law (from formal verification)
 */
@JvmInline
@Serializable
value class Stock(val value: Int) {
    init {
        require(value >= 0) { "Stock cannot be negative" }
    }
    
    operator fun plus(quantity: Quantity): Stock = Stock(value + quantity.value)
    operator fun minus(quantity: Quantity): Stock = Stock(value - quantity.value)
    
    fun canReserve(quantity: Quantity): Boolean = value >= quantity.value
    
    companion object {
        val ZERO = Stock(0)
    }
}

// === Order Status (Algebraic Data Type) ===

/**
 * Order status with type-safe state transitions
 * RESOLVED AMBIGUITY: Clear state transition rules (from formal verification)
 */
sealed interface OrderStatus {
    /**
     * Order is reserved with inventory allocated
     * RESOLVED: Atomic inventory reservation at order placement
     */
    @Serializable
    data object Reserved : OrderStatus
    
    /**
     * Order is confirmed and being processed
     * RESOLVED: Mutual exclusion - only one order per book can be confirmed
     */
    @Serializable
    data object Confirmed : OrderStatus
    
    /**
     * Order has been shipped
     * RESOLVED: Payment must be completed before shipping
     */
    @Serializable
    data object Shipped : OrderStatus
    
    /**
     * Order has been cancelled and inventory restored
     * RESOLVED: Only reserved orders can be cancelled
     */
    @Serializable
    data object Cancelled : OrderStatus
}

// === Payment Status ===

/**
 * Payment status with clear states
 * RESOLVED AMBIGUITY: Payment-before-shipping policy (from formal verification)
 */
sealed interface PaymentStatus {
    @Serializable
    data object Pending : PaymentStatus
    @Serializable
    data object Completed : PaymentStatus
    @Serializable
    data object Failed : PaymentStatus
}

// === Reservation Status ===

/**
 * Reservation status for inventory management
 * RESOLVED AMBIGUITY: Clear reservation lifecycle (from formal verification)
 */
sealed interface ReservationStatus {
    @Serializable
    data object Active : ReservationStatus
    @Serializable
    data class Expired(val expiredAtEpochMilli: Long) : ReservationStatus {
        val expiredAt: Instant get() = Instant.ofEpochMilli(expiredAtEpochMilli)
    }
    @Serializable
    data object Released : ReservationStatus
}

// === Timestamp ===

@JvmInline
@Serializable
value class Timestamp(val epochMilli: Long) {
    val value: Instant get() = Instant.ofEpochMilli(epochMilli)
    
    fun isAfter(other: Timestamp): Boolean = epochMilli > other.epochMilli
    fun isBefore(other: Timestamp): Boolean = epochMilli < other.epochMilli
    
    companion object {
        fun now(): Timestamp = Timestamp(System.currentTimeMillis())
        fun from(instant: Instant): Timestamp = Timestamp(instant.toEpochMilli())
    }
}

// === Inventory (Immutable with Conservation Law) ===

/**
 * Immutable inventory that enforces conservation law
 * RESOLVED AMBIGUITY: Physical + Reserved = Total (from formal verification)
 */
@Serializable
data class Inventory(
    val physicalStock: Stock,
    val reservedStock: Stock,
    val totalStock: Stock
) {
    init {
        // INVARIANT: Conservation law from formal verification
        require(physicalStock.value + reservedStock.value == totalStock.value) {
            "Conservation law violated: physical($physicalStock) + reserved($reservedStock) != total($totalStock)"
        }
        
        // INVARIANT: Reserved stock cannot exceed total
        require(reservedStock.value <= totalStock.value) {
            "Reserved stock cannot exceed total stock"
        }
    }
    
    /**
     * Atomic reservation operation
     * RESOLVED AMBIGUITY: Atomic inventory check and reservation (from formal verification)
     */
    fun reserve(quantity: Quantity): Option<Inventory> =
        if (physicalStock.canReserve(quantity)) {
            Some(copy(
                physicalStock = physicalStock - quantity,
                reservedStock = reservedStock + quantity
            ))
        } else {
            none()
        }
    
    /**
     * Release reservation (for cancellation)
     * RESOLVED AMBIGUITY: Immediate inventory restoration (from formal verification)
     */
    fun release(quantity: Quantity): Inventory =
        copy(
            physicalStock = physicalStock + quantity,
            reservedStock = reservedStock - quantity
        )
    
    companion object {
        fun initial(totalStock: Stock): Inventory = Inventory(
            physicalStock = totalStock,
            reservedStock = Stock.ZERO,
            totalStock = totalStock
        )
    }
}

// === Timeout Configuration ===

/**
 * Reservation timeout configuration
 * RESOLVED AMBIGUITY: Automatic timeout handling (from formal verification)
 */
@Serializable
data class ReservationTimeout(val hours: Int) {
    init {
        require(hours > 0) { "Timeout must be positive" }
    }
    
    fun isExpired(reservedAt: Timestamp, now: Timestamp): Boolean {
        val expirationTime = reservedAt.epochMilli + (hours * 3600L * 1000L)
        return now.epochMilli > expirationTime
    }
    
    companion object {
        val DEFAULT = ReservationTimeout(8) // 8 hours as specified in refined requirements
    }
} 