package com.bookstore.domain

import arrow.core.fold
import io.kotest.core.spec.style.StringSpec
import io.kotest.matchers.shouldBe
import io.kotest.property.Arb
import io.kotest.property.arbitrary.*
import io.kotest.property.checkAll

/**
 * Property-based tests that verify formal properties from TLA+ specifications
 * These tests ensure that the constraints discovered in formal verification
 * are maintained in the Kotlin implementation.
 */
class FormalVerificationPropertiesTest : StringSpec({
    
    // === Test Data Generators ===
    
    val arbBookId = Arb.string(1, 10).map { BookId("book-$it") }
    val arbCustomerId = Arb.string(1, 10).map { CustomerId("customer-$it") }
    val arbISBN = Arb.string(10).map { "978-$it" }.map { ISBN(it) }
    val arbMoney = Arb.long(0L, 100000L).map { Money(it) }
    val arbQuantity = Arb.int(1, 10).map { Quantity(it) }
    val arbStock = Arb.int(0, 100).map { Stock(it) }
    val arbTotalStock = Arb.int(1, 100).map { Stock(it) }
    
    // === Property 1: Inventory Conservation Law ===
    // FORMAL PROPERTY: Physical + Reserved = Total (always)
    
    "Inventory conservation law must always hold" {
        checkAll(arbTotalStock) { totalStock ->
            val inventory = Inventory.initial(totalStock)
            
            // Initial state: physical = total, reserved = 0
            inventory.physicalStock.value + inventory.reservedStock.value shouldBe totalStock.value
            
            // After any valid reservation
            checkAll(arbQuantity) { quantity ->
                inventory.reserve(quantity).fold(
                    ifEmpty = { 
                        // If reservation fails, inventory should be unchanged
                        inventory.physicalStock.value + inventory.reservedStock.value shouldBe totalStock.value
                    },
                    ifSome = { newInventory ->
                        // If reservation succeeds, conservation law must hold
                        newInventory.physicalStock.value + newInventory.reservedStock.value shouldBe totalStock.value
                    }
                )
            }
        }
    }
    
    // === Property 2: Reserved Stock Consistency ===
    // FORMAL PROPERTY: Reserved stock never exceeds total stock
    
    "Reserved stock never exceeds total stock" {
        checkAll(arbTotalStock, arbQuantity) { totalStock, quantity ->
            val inventory = Inventory.initial(totalStock)
            
            inventory.reserve(quantity).fold(
                ifEmpty = { 
                    // Reservation should fail if quantity > available stock
                    (quantity.value > inventory.physicalStock.value) shouldBe true
                },
                ifSome = { newInventory ->
                    // If reservation succeeds, reserved stock should not exceed total
                    newInventory.reservedStock.value shouldBe quantity.value
                    (newInventory.reservedStock.value <= totalStock.value) shouldBe true
                }
            )
        }
    }
    
    // === Property 3: Atomic Reservation Operation ===
    // FORMAL PROPERTY: Inventory check and reservation are atomic
    
    "Inventory reservation is atomic - either succeeds completely or fails completely" {
        checkAll(arbTotalStock, arbQuantity) { totalStock, quantity ->
            val inventory = Inventory.initial(totalStock)
            val originalPhysical = inventory.physicalStock.value
            val originalReserved = inventory.reservedStock.value
            
            inventory.reserve(quantity).fold(
                ifEmpty = {
                    // If fails, inventory should be completely unchanged
                    inventory.physicalStock.value shouldBe originalPhysical
                    inventory.reservedStock.value shouldBe originalReserved
                },
                ifSome = { newInventory ->
                    // If succeeds, both physical and reserved should be updated atomically
                    newInventory.physicalStock.value shouldBe originalPhysical - quantity.value
                    newInventory.reservedStock.value shouldBe originalReserved + quantity.value
                }
            )
        }
    }
    
    // === Property 4: Order State Transition Validity ===
    // FORMAL PROPERTY: Only valid state transitions are allowed
    
    "Order state transitions follow formal specification rules" {
        checkAll(arbCustomerId, arbBookId, arbQuantity) { customerId, bookId, quantity ->
            val order = Order.create(customerId, bookId, quantity)
            
            // Initial state should be Reserved
            order.status shouldBe OrderStatus.Reserved
            order.paymentStatus shouldBe PaymentStatus.Pending
            order.reservationStatus shouldBe ReservationStatus.Active
            
            // Reserved -> Confirmed should succeed
            val confirmedResult = order.confirm()
            confirmedResult.isRight() shouldBe true
            
            // Reserved -> Cancelled should succeed
            val cancelledResult = order.cancel()
            cancelledResult.isRight() shouldBe true
        }
    }
    
    // === Property 5: Payment Before Shipping Policy ===
    // FORMAL PROPERTY: Orders cannot be shipped without completed payment
    
    "Orders cannot be shipped without completed payment" {
        checkAll(arbCustomerId, arbBookId, arbQuantity) { customerId, bookId, quantity ->
            val order = Order.create(customerId, bookId, quantity)
            val confirmedOrder = order.confirm().fold(
                ifLeft = { order },
                ifRight = { it }
            )
            
            // Shipping should fail with pending payment
            confirmedOrder.paymentStatus shouldBe PaymentStatus.Pending
            val shipResult = confirmedOrder.ship()
            shipResult.isLeft() shouldBe true
            
            // Shipping should succeed only after payment completion
            val paidOrder = confirmedOrder.completePayment().fold(
                ifLeft = { confirmedOrder },
                ifRight = { it }
            )
            paidOrder.paymentStatus shouldBe PaymentStatus.Completed
            val shipWithPaymentResult = paidOrder.ship()
            shipWithPaymentResult.isRight() shouldBe true
        }
    }
    
    // === Property 6: Cancellation Rules ===
    // FORMAL PROPERTY: Only reserved orders can be cancelled
    
    "Only reserved orders can be cancelled" {
        checkAll(arbCustomerId, arbBookId, arbQuantity) { customerId, bookId, quantity ->
            val order = Order.create(customerId, bookId, quantity)
            
            // Reserved order can be cancelled
            order.status shouldBe OrderStatus.Reserved
            val cancelResult = order.cancel()
            cancelResult.isRight() shouldBe true
            
            // Confirmed order cannot be cancelled
            val confirmedOrder = order.confirm().fold(
                ifLeft = { order },
                ifRight = { it }
            )
            confirmedOrder.status shouldBe OrderStatus.Confirmed
            val cancelConfirmedResult = confirmedOrder.cancel()
            cancelConfirmedResult.isLeft() shouldBe true
        }
    }
}) 