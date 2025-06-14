// Bookstore System - Alloy Specification
// This specification reveals ambiguities in the natural language requirements

// Basic entities
sig Book {
    isbn: one ISBN,
    title: one String,
    price: one Money
}

sig ISBN {}
sig String {}
sig Money {}

sig Customer {
    name: one String,
    email: one String,
    address: one Address,
    orders: set Order
}

sig Address {
    street: one String,
    city: one String,
    zipCode: one String
}

// Inventory management
sig Inventory {
    book: one Book,
    physicalStock: one Int,
    reservedStock: one Int
} {
    // Basic constraints
    physicalStock >= 0
    reservedStock >= 0
    reservedStock <= physicalStock
}

// Order management
sig Order {
    customer: one Customer,
    items: set OrderItem,
    status: one OrderStatus,
    createdAt: one Time
} {
    // An order must have at least one item
    some items
}

sig OrderItem {
    book: one Book,
    quantity: one Int,
    order: one Order
} {
    quantity > 0
}

// Order status - reveals ambiguity about state transitions
abstract sig OrderStatus {}
one sig Pending, Confirmed, Shipped, Cancelled extends OrderStatus {}

sig Time {}

// Payment processing
sig Payment {
    order: one Order,
    amount: one Money,
    status: one PaymentStatus,
    processedAt: one Time
}

abstract sig PaymentStatus {}
one sig PaymentPending, PaymentCompleted, PaymentFailed extends PaymentStatus {}

// CONSTRAINTS - These reveal the ambiguities in natural language requirements

// AMBIGUITY 1: "在庫がある本のみ注文可能" - What about concurrent orders?
fact StockAvailabilityConstraint {
    // This constraint is TOO WEAK - it doesn't handle concurrent orders properly
    all oi: OrderItem | {
        oi.order.status in (Confirmed + Shipped) implies {
            some inv: Inventory | inv.book = oi.book and inv.physicalStock >= oi.quantity
        }
    }
    // PROBLEM: Two pending orders for the same book can both be confirmed
    // even if total quantity exceeds available stock
}

// AMBIGUITY 2: "注文後、在庫から商品を引き当てる" - When exactly?
fact InventoryAllocationTiming {
    // UNCLEAR: Is allocation at order creation or confirmation?
    // This constraint assumes allocation happens at confirmation
    all inv: Inventory | {
        let confirmedItems = { oi: OrderItem | 
            oi.book = inv.book and oi.order.status in (Confirmed + Shipped) } |
        let totalConfirmed = sum oi: confirmedItems | oi.quantity |
        inv.reservedStock >= totalConfirmed
    }
    // PROBLEM: What happens between order creation and confirmation?
}

// AMBIGUITY 3: "同じ本を複数の顧客が同時に注文することがある" - How to handle?
fact ConcurrentOrderHandling {
    // This constraint doesn't specify HOW concurrent orders are handled
    // It only states that overbooking shouldn't happen
    all b: Book | {
        let allConfirmedOrders = { oi: OrderItem | 
            oi.book = b and oi.order.status in (Confirmed + Shipped) } |
        let totalOrdered = sum oi: allConfirmedOrders | oi.quantity |
        let availableStock = sum inv: Inventory | 
            (inv.book = b) => inv.physicalStock else 0 |
        totalOrdered <= availableStock
    }
    // PROBLEM: No specification of ordering, priority, or conflict resolution
}

// AMBIGUITY 4: "注文確定後はキャンセル可能" - Until when?
fact CancellationConstraint {
    // UNCLEAR: Can orders be cancelled after shipping?
    all o: Order | {
        o.status = Cancelled implies {
            // What was the previous status? Any status can be cancelled?
            o.status.prev in (Pending + Confirmed + Shipped) // This is not valid Alloy syntax
        }
    }
    // PROBLEM: No clear state transition rules
}

// AMBIGUITY 5: "キャンセル時は在庫を復元する" - When and how?
fact StockRestorationOnCancellation {
    // UNCLEAR: Immediate restoration? What about other waiting orders?
    all o: Order | {
        o.status = Cancelled implies {
            all oi: o.items | {
                some inv: Inventory | {
                    inv.book = oi.book
                    // How is stock restored? This doesn't specify the mechanism
                }
            }
        }
    }
    // PROBLEM: No specification of restoration timing or impact on other orders
}

// AMBIGUITY 6: Payment and order confirmation relationship
fact PaymentOrderRelationship {
    // UNCLEAR: Must payment complete before order confirmation?
    all o: Order | {
        o.status = Confirmed implies {
            some p: Payment | p.order = o and p.status = PaymentCompleted
        }
    }
    // PROBLEM: What if payment fails after confirmation?
}

// Reference integrity constraints
fact CustomerOrderRelation {
    all o: Order | o in o.customer.orders
    all c: Customer | all o: c.orders | o.customer = c
}

fact OrderItemConsistency {
    all oi: OrderItem | oi in oi.order.items
    all o: Order | all oi: o.items | oi.order = o
}

// PROBLEMATIC SCENARIOS TO EXPLORE

// Scenario 1: Race condition in stock allocation
run RaceConditionScenario {
    some disj o1, o2: Order |
        o1.status = Pending and o2.status = Pending and
        some oi1: o1.items, oi2: o2.items | 
            oi1.book = oi2.book and
            (oi1.quantity + oi2.quantity) > 
                (sum inv: Inventory | (inv.book = oi1.book) => inv.physicalStock else 0)
} for 4

// Scenario 2: Inconsistent inventory state
run InconsistentInventoryScenario {
    some inv: Inventory |
        inv.reservedStock > inv.physicalStock
} for 3

// Scenario 3: Order without proper payment
run OrderWithoutPaymentScenario {
    some o: Order |
        o.status = Confirmed and
        no p: Payment | p.order = o and p.status = PaymentCompleted
} for 3

// ASSERTIONS TO CHECK (these will likely fail, revealing problems)

assert NoOverbooking {
    all b: Book | {
        let totalConfirmed = sum oi: OrderItem | 
            (oi.book = b and oi.order.status in (Confirmed + Shipped)) => oi.quantity else 0 |
        let totalStock = sum inv: Inventory | 
            (inv.book = b) => inv.physicalStock else 0 |
        totalConfirmed <= totalStock
    }
}

assert InventoryConsistency {
    all inv: Inventory |
        inv.reservedStock <= inv.physicalStock and
        inv.reservedStock >= 0 and
        inv.physicalStock >= 0
}

assert PaymentOrderConsistency {
    all o: Order |
        o.status = Confirmed implies
            some p: Payment | p.order = o and p.status = PaymentCompleted
}

// Check assertions (these will reveal problems)
check NoOverbooking for 5
check InventoryConsistency for 5
check PaymentOrderConsistency for 5 