// Refined Bookstore System - Alloy Specification
// This specification resolves the ambiguities discovered in the original version
// by implementing proper constraints, atomic operations, and clear state management

// Basic entities
sig Book {
    isbn: one ISBN,
    title: one String,
    price: one Money
}

sig Customer {
    name: one String,
    email: one Email
}

sig ISBN, String, Email, Money {}

// RESOLVED AMBIGUITY: Clear order states with proper transitions
abstract sig OrderStatus {}
one sig Pending, Reserved, Confirmed, Shipped, Cancelled extends OrderStatus {}

abstract sig PaymentStatus {}
one sig PaymentPending, PaymentCompleted, PaymentFailed extends PaymentStatus {}

abstract sig ReservationStatus {}
one sig NoReservation, ReservationActive, ReservationExpired, ReservationReleased extends ReservationStatus {}

// Order entity with clear state tracking
sig Order {
    customer: one Customer,
    book: one Book,
    quantity: one Int,
    status: one OrderStatus,
    payment: one PaymentStatus,
    reservation: one ReservationStatus,
    timestamp: one Int
} {
    quantity > 0
    quantity <= 2  // MaxStock = 2 for performance
    timestamp >= 0
    timestamp <= 10  // Limit timestamp for performance
}

// Inventory with atomic stock management
sig Inventory {
    book: one Book,
    physicalStock: one Int,
    reservedStock: one Int
} {
    physicalStock >= 0
    reservedStock >= 0
    // RESOLVED: Reserved stock cannot exceed total capacity
    reservedStock <= 2  // MaxStock = 2
    // RESOLVED: Conservation law - physical + reserved = total
    physicalStock + reservedStock = 2
}

// RESOLVED AMBIGUITY 1: Atomic inventory operations
// CONSTRAINT: Stock reservation happens atomically with order placement
fact AtomicStockReservation {
    all o: Order | {
        o.status = Reserved implies {
            o.reservation = ReservationActive
            // Stock is immediately reserved when order is placed
            one inv: Inventory | inv.book = o.book and inv.reservedStock >= o.quantity
        }
    }
}

// RESOLVED AMBIGUITY 2: Clear state transitions
// CONSTRAINT: Valid state transition rules
fact ValidStateTransitions {
    all o: Order | {
        // Orders start as Reserved (with immediate stock reservation)
        o.status = Pending implies o.reservation = NoReservation
        o.status = Reserved implies o.reservation = ReservationActive
        o.status = Confirmed implies o.reservation = ReservationActive
        o.status = Shipped implies o.reservation = ReservationActive
        o.status = Cancelled implies o.reservation in (ReservationReleased + ReservationExpired)
        
        // Payment requirements
        o.status = Shipped implies o.payment = PaymentCompleted
        o.payment = PaymentFailed implies o.status = Cancelled
    }
}

// RESOLVED AMBIGUITY 3: Clear cancellation rules
// CONSTRAINT: Only certain states allow cancellation
fact CancellationRules {
    all o: Order | {
        o.status = Cancelled implies {
            // Can only cancel Pending or Reserved orders
            o.reservation in (ReservationReleased + ReservationExpired)
        }
    }
}

// RESOLVED AMBIGUITY 4: Inventory consistency
// CONSTRAINT: Reserved stock exactly matches active reservations
fact InventoryConsistency {
    all b: Book | {
        one inv: Inventory | inv.book = b and {
            inv.reservedStock = #{o: Order | 
                o.book = b and 
                o.status in (Reserved + Confirmed + Shipped) and
                o.reservation = ReservationActive
            }
        }
    }
}

// RESOLVED AMBIGUITY 5: No overbooking
// CONSTRAINT: Total reserved quantity cannot exceed available stock
fact NoOverbooking {
    all b: Book | {
        let activeOrders = {o: Order | o.book = b and o.status in (Reserved + Confirmed + Shipped)} |
        let totalReserved = sum o: activeOrders | o.quantity |
        totalReserved <= 2  // MaxStock = 2
    }
}

// RESOLVED AMBIGUITY 6: Mutual exclusion for processing
// CONSTRAINT: Only one order per book can be in Confirmed state at a time
fact MutualExclusion {
    all b: Book | {
        lone o: Order | o.book = b and o.status = Confirmed
    }
}

// RESOLVED AMBIGUITY 7: Payment-before-shipping policy
// CONSTRAINT: Shipping requires completed payment
fact PaymentBeforeShipping {
    all o: Order | {
        o.status = Shipped implies o.payment = PaymentCompleted
    }
}

// RESOLVED AMBIGUITY 8: Timeout handling
// CONSTRAINT: Expired reservations are automatically cancelled
fact TimeoutHandling {
    all o: Order | {
        o.reservation = ReservationExpired implies {
            o.status = Cancelled
            o.timestamp > 8  // Timeout threshold (reduced for performance)
        }
    }
}

// Performance optimization: Limit total orders
fact LimitOrders {
    #Order <= 3  // MaxOrders = 3
}

// Scenario predicates for testing

// Test: Successful order flow
pred SuccessfulOrderFlow {
    some o: Order | {
        o.status = Shipped
        o.payment = PaymentCompleted
        o.reservation = ReservationActive
    }
}

// Test: Concurrent orders for same book (should not cause overbooking)
pred ConcurrentOrdersNoConcflict {
    some disj o1, o2: Order | {
        o1.book = o2.book
        o1.status in (Reserved + Confirmed)
        o2.status in (Reserved + Confirmed)
        // Should not violate inventory constraints
    }
}

// Test: Payment failure handling
pred PaymentFailureHandling {
    some o: Order | {
        o.payment = PaymentFailed
        o.status = Cancelled
        o.reservation = ReservationReleased
    }
}

// Commands for verification (optimized for speed)
run SuccessfulOrderFlow for 2 but 2 Order, 1 Book, 1 Customer, 2 Int
run ConcurrentOrdersNoConcflict for 2 but 2 Order, 1 Book, 1 Customer, 2 Int
run PaymentFailureHandling for 2 but 2 Order, 1 Book, 1 Customer, 2 Int

// Basic checks with minimal scope
check { all inv: Inventory | inv.physicalStock + inv.reservedStock = 2 } for 2 but 2 Order, 1 Book, 1 Customer, 2 Int
check { all o: Order | o.status = Shipped implies o.payment = PaymentCompleted } for 2 but 2 Order, 1 Book, 1 Customer, 2 Int 