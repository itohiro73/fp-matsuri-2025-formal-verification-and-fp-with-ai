package com.bookstore.domain

import arrow.core.Either
import arrow.core.flatMap
import arrow.core.left
import arrow.core.right
import arrow.fx.coroutines.Resource
import kotlinx.coroutines.sync.Mutex
import kotlinx.coroutines.sync.withLock

/**
 * Domain services that orchestrate complex business operations
 * All operations maintain functional programming principles and formal verification constraints
 */

// === Repository Interfaces ===

interface BookInventoryRepository {
    suspend fun findByBookId(bookId: BookId): Either<DomainError, BookInventory>
    suspend fun save(bookInventory: BookInventory): Either<DomainError, BookInventory>
}

interface OrderRepository {
    suspend fun findById(orderId: OrderId): Either<DomainError, Order>
    suspend fun save(order: Order): Either<DomainError, Order>
    suspend fun findActiveReservationsByBookId(bookId: BookId): Either<DomainError, List<Order>>
    suspend fun findExpiredReservations(timeout: ReservationTimeout): Either<DomainError, List<Order>>
}

interface CustomerRepository {
    suspend fun findById(customerId: CustomerId): Either<DomainError, Customer>
}

// === Domain Events ===

sealed interface DomainEvent {
    val timestamp: Timestamp
    
    data class OrderPlaced(
        val orderId: OrderId,
        val customerId: CustomerId,
        val bookId: BookId,
        val quantity: Quantity,
        override val timestamp: Timestamp = Timestamp.now()
    ) : DomainEvent
    
    data class OrderConfirmed(
        val orderId: OrderId,
        override val timestamp: Timestamp = Timestamp.now()
    ) : DomainEvent
    
    data class OrderShipped(
        val orderId: OrderId,
        override val timestamp: Timestamp = Timestamp.now()
    ) : DomainEvent
    
    data class OrderCancelled(
        val orderId: OrderId,
        val reason: String,
        override val timestamp: Timestamp = Timestamp.now()
    ) : DomainEvent
    
    data class PaymentCompleted(
        val orderId: OrderId,
        override val timestamp: Timestamp = Timestamp.now()
    ) : DomainEvent
    
    data class PaymentFailed(
        val orderId: OrderId,
        val reason: String,
        override val timestamp: Timestamp = Timestamp.now()
    ) : DomainEvent
    
    data class ReservationExpired(
        val orderId: OrderId,
        override val timestamp: Timestamp = Timestamp.now()
    ) : DomainEvent
}

// === Event Publisher ===

interface DomainEventPublisher {
    suspend fun publish(event: DomainEvent): Either<DomainError, Unit>
}

// === Order Service ===

/**
 * Order service that orchestrates order operations with formal verification constraints
 */
class OrderService(
    private val bookInventoryRepository: BookInventoryRepository,
    private val orderRepository: OrderRepository,
    private val customerRepository: CustomerRepository,
    private val eventPublisher: DomainEventPublisher
) {
    
    // Mutex for ensuring atomic operations (simulating database transactions)
    private val orderMutex = Mutex()
    
    /**
     * Place an order with atomic inventory reservation
     * RESOLVED AMBIGUITY: Atomic inventory check and reservation at order placement
     */
    suspend fun placeOrder(
        customerId: CustomerId,
        bookId: BookId,
        quantity: Quantity
    ): Either<DomainError, Order> = orderMutex.withLock {
        customerRepository.findById(customerId).flatMap { customer ->
            bookInventoryRepository.findByBookId(bookId).flatMap { bookInventory ->
                bookInventory.placeOrder(customerId, quantity).flatMap { (updatedInventory, order) ->
                    bookInventoryRepository.save(updatedInventory).flatMap {
                        orderRepository.save(order).flatMap { savedOrder ->
                            eventPublisher.publish(
                                DomainEvent.OrderPlaced(
                                    orderId = savedOrder.id,
                                    customerId = customerId,
                                    bookId = bookId,
                                    quantity = quantity
                                )
                            ).map { savedOrder }
                        }
                    }
                }
            }
        }
    }
    
    /**
     * Confirm an order with mutual exclusion
     * RESOLVED AMBIGUITY: Mutual exclusion for order processing
     */
    suspend fun confirmOrder(orderId: OrderId): Either<DomainError, Order> = orderMutex.withLock {
        orderRepository.findById(orderId).flatMap { order ->
            bookInventoryRepository.findByBookId(order.bookId).flatMap { bookInventory ->
                bookInventory.startProcessing(orderId).flatMap { processingInventory ->
                    order.confirm().flatMap { confirmedOrder ->
                        bookInventoryRepository.save(processingInventory).flatMap {
                            orderRepository.save(confirmedOrder).flatMap { savedOrder ->
                                eventPublisher.publish(
                                    DomainEvent.OrderConfirmed(orderId = savedOrder.id)
                                ).map { savedOrder }
                            }
                        }
                    }
                }
            }
        }
    }
    
    /**
     * Ship an order (requires completed payment)
     * RESOLVED AMBIGUITY: Payment must be completed before shipping
     */
    suspend fun shipOrder(orderId: OrderId): Either<DomainError, Order> = orderMutex.withLock {
        orderRepository.findById(orderId).flatMap { order ->
            order.ship().flatMap { shippedOrder ->
                bookInventoryRepository.findByBookId(order.bookId).flatMap { bookInventory ->
                    val finishedInventory = bookInventory.finishProcessing()
                    bookInventoryRepository.save(finishedInventory).flatMap {
                        orderRepository.save(shippedOrder).flatMap { savedOrder ->
                            eventPublisher.publish(
                                DomainEvent.OrderShipped(orderId = savedOrder.id)
                            ).map { savedOrder }
                        }
                    }
                }
            }
        }
    }
    
    /**
     * Cancel an order with immediate inventory restoration
     * RESOLVED AMBIGUITY: Only reserved orders can be cancelled, immediate inventory restoration
     */
    suspend fun cancelOrder(orderId: OrderId, reason: String): Either<DomainError, Order> = orderMutex.withLock {
        orderRepository.findById(orderId).flatMap { order ->
            bookInventoryRepository.findByBookId(order.bookId).flatMap { bookInventory ->
                bookInventory.cancelOrder(order).flatMap { (updatedInventory, cancelledOrder) ->
                    bookInventoryRepository.save(updatedInventory).flatMap {
                        orderRepository.save(cancelledOrder).flatMap { savedOrder ->
                            eventPublisher.publish(
                                DomainEvent.OrderCancelled(orderId = savedOrder.id, reason = reason)
                            ).map { savedOrder }
                        }
                    }
                }
            }
        }
    }
}

// === Payment Service ===

/**
 * Payment service that handles payment operations with automatic cancellation on failure
 */
class PaymentService(
    private val bookInventoryRepository: BookInventoryRepository,
    private val orderRepository: OrderRepository,
    private val eventPublisher: DomainEventPublisher
) {
    
    private val paymentMutex = Mutex()
    
    /**
     * Complete payment for an order
     */
    suspend fun completePayment(orderId: OrderId): Either<DomainError, Order> = paymentMutex.withLock {
        orderRepository.findById(orderId).flatMap { order ->
            order.completePayment().flatMap { paidOrder ->
                orderRepository.save(paidOrder).flatMap { savedOrder ->
                    eventPublisher.publish(
                        DomainEvent.PaymentCompleted(orderId = savedOrder.id)
                    ).map { savedOrder }
                }
            }
        }
    }
    
    /**
     * Handle payment failure with automatic cancellation and inventory restoration
     * RESOLVED AMBIGUITY: Payment failure triggers automatic cancellation
     */
    suspend fun failPayment(orderId: OrderId, reason: String): Either<DomainError, Order> = paymentMutex.withLock {
        orderRepository.findById(orderId).flatMap { order ->
            bookInventoryRepository.findByBookId(order.bookId).flatMap { bookInventory ->
                bookInventory.handlePaymentFailure(order).flatMap { (updatedInventory, failedOrder) ->
                    bookInventoryRepository.save(updatedInventory).flatMap {
                        orderRepository.save(failedOrder).flatMap { savedOrder ->
                            eventPublisher.publish(
                                DomainEvent.PaymentFailed(orderId = savedOrder.id, reason = reason)
                            ).map { savedOrder }
                        }
                    }
                }
            }
        }
    }
}

// === Reservation Timeout Service ===

/**
 * Service that handles reservation timeouts
 * RESOLVED AMBIGUITY: Automatic timeout handling with inventory restoration
 */
class ReservationTimeoutService(
    private val bookInventoryRepository: BookInventoryRepository,
    private val orderRepository: OrderRepository,
    private val eventPublisher: DomainEventPublisher,
    private val timeout: ReservationTimeout = ReservationTimeout.DEFAULT
) {
    
    private val timeoutMutex = Mutex()
    
    /**
     * Process expired reservations
     */
    suspend fun processExpiredReservations(): Either<DomainError, List<Order>> = timeoutMutex.withLock {
        orderRepository.findExpiredReservations(timeout).flatMap { expiredOrders ->
            val results = expiredOrders.map { order ->
                processExpiredReservation(order)
            }
            
            // Collect all successful results
            val successes = mutableListOf<Order>()
            for (result in results) {
                when (result) {
                    is Either.Left -> return@withLock result
                    is Either.Right -> successes.add(result.value)
                }
            }
            
            successes.right()
        }
    }
    
    private suspend fun processExpiredReservation(order: Order): Either<DomainError, Order> =
        bookInventoryRepository.findByBookId(order.bookId).flatMap { bookInventory ->
            bookInventory.handleTimeout(order, timeout).flatMap { (updatedInventory, expiredOrder) ->
                bookInventoryRepository.save(updatedInventory).flatMap {
                    orderRepository.save(expiredOrder).flatMap { savedOrder ->
                        eventPublisher.publish(
                            DomainEvent.ReservationExpired(orderId = savedOrder.id)
                        ).map { savedOrder }
                    }
                }
            }
        }
}

// === Inventory Query Service ===

/**
 * Service for querying inventory information
 */
class InventoryQueryService(
    private val bookInventoryRepository: BookInventoryRepository,
    private val orderRepository: OrderRepository
) {
    
    /**
     * Get current inventory status for a book
     */
    suspend fun getInventoryStatus(bookId: BookId): Either<DomainError, InventoryStatus> =
        bookInventoryRepository.findByBookId(bookId).flatMap { bookInventory ->
            orderRepository.findActiveReservationsByBookId(bookId).map { activeOrders ->
                InventoryStatus(
                    bookId = bookId,
                    physicalStock = bookInventory.inventory.physicalStock,
                    reservedStock = bookInventory.inventory.reservedStock,
                    totalStock = bookInventory.inventory.totalStock,
                    activeReservations = activeOrders.size,
                    isProcessing = bookInventory.processingOrderId != null
                )
            }
        }
    
    /**
     * Check if a book has sufficient stock for a given quantity
     */
    suspend fun hasAvailableStock(bookId: BookId, quantity: Quantity): Either<DomainError, Boolean> =
        bookInventoryRepository.findByBookId(bookId).map { bookInventory ->
            bookInventory.inventory.physicalStock.canReserve(quantity)
        }
}

// === Data Transfer Objects ===

/**
 * Inventory status for queries
 */
data class InventoryStatus(
    val bookId: BookId,
    val physicalStock: Stock,
    val reservedStock: Stock,
    val totalStock: Stock,
    val activeReservations: Int,
    val isProcessing: Boolean
) 