---- MODULE BookstoreSystemRefined ----
\* Refined Bookstore System - TLA+ Specification
\* This specification resolves the ambiguities discovered in the original version
\* by implementing atomic operations, proper concurrency control, and clear state transitions

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS
    Books,          \* Set of book IDs
    Customers,      \* Set of customer IDs
    MaxStock,       \* Maximum stock per book
    MaxOrders       \* Maximum number of orders

VARIABLES
    inventory,      \* Function: [Books -> [physicalStock: Nat, reservedStock: Nat]]
    orders,         \* Sequence of orders
    orderStatus,    \* Function: [OrderId -> OrderStatus]
    payments,       \* Function: [OrderId -> PaymentStatus]
    processing,     \* Set of orders currently being processed (mutual exclusion)
    reservations,   \* Function: [OrderId -> ReservationStatus] - tracks inventory reservations
    timestamp       \* Current logical timestamp

\* Order, payment, and reservation status definitions
OrderStatuses == {"pending", "reserved", "confirmed", "shipped", "cancelled"}
PaymentStatuses == {"pending", "completed", "failed"}
ReservationStatuses == {"none", "reserved", "expired", "released"}

\* Type invariant
TypeInvariant ==
    /\ inventory \in [Books -> [physicalStock: Nat, reservedStock: Nat]]
    /\ orders \in Seq([customer: Customers, book: Books, quantity: Nat])
    /\ orderStatus \in [1..Len(orders) -> OrderStatuses]
    /\ payments \in [1..Len(orders) -> PaymentStatuses]
    /\ reservations \in [1..Len(orders) -> ReservationStatuses]
    /\ processing \subseteq 1..Len(orders)
    /\ timestamp \in Nat

\* Initial state
Init ==
    /\ inventory = [b \in Books |-> [physicalStock |-> MaxStock, reservedStock |-> 0]]
    /\ orders = <<>>
    /\ orderStatus = <<>>
    /\ payments = <<>>
    /\ reservations = <<>>
    /\ processing = {}
    /\ timestamp = 0

\* RESOLVED AMBIGUITY 1: Atomic inventory reservation at order placement
\* SOLUTION: Check and reserve inventory atomically when placing order
PlaceOrderWithReservation(customer, book, quantity) ==
    /\ quantity > 0
    /\ quantity <= MaxStock
    /\ Len(orders) < MaxOrders
    \* ATOMIC OPERATION: Check availability and reserve immediately
    /\ inventory[book].physicalStock >= quantity
    /\ LET orderIndex == Len(orders) + 1 IN
        /\ orders' = Append(orders, [customer |-> customer, book |-> book, quantity |-> quantity])
        /\ orderStatus' = Append(orderStatus, "reserved")
        /\ payments' = Append(payments, "pending")
        /\ reservations' = Append(reservations, "reserved")
        \* ATOMIC INVENTORY UPDATE: Reserve stock immediately
        /\ inventory' = [inventory EXCEPT 
            ![book].physicalStock = @ - quantity,
            ![book].reservedStock = @ + quantity]
        /\ timestamp' = timestamp + 1
        /\ UNCHANGED processing

\* RESOLVED AMBIGUITY 2: Clear mutual exclusion for order processing
\* SOLUTION: Only one order per book can be processed at a time
ConfirmReservedOrder(orderIndex) ==
    /\ orderIndex \in 1..Len(orders)
    /\ orderStatus[orderIndex] = "reserved"
    /\ reservations[orderIndex] = "reserved"
    /\ orderIndex \notin processing
    /\ LET order == orders[orderIndex] IN
        \* MUTUAL EXCLUSION: Ensure no other order for same book is being processed
        /\ ~\E i \in processing : orders[i].book = order.book
        /\ orderStatus' = [orderStatus EXCEPT ![orderIndex] = "confirmed"]
        /\ processing' = processing \cup {orderIndex}
        /\ timestamp' = timestamp + 1
        /\ UNCHANGED <<inventory, orders, payments, reservations>>

\* RESOLVED AMBIGUITY 3: Payment must complete before shipping
\* SOLUTION: Enforce payment-first policy
ProcessPayment(orderIndex) ==
    /\ orderIndex \in 1..Len(orders)
    /\ payments[orderIndex] = "pending"
    /\ orderStatus[orderIndex] \in {"reserved", "confirmed"}
    /\ \/ /\ payments' = [payments EXCEPT ![orderIndex] = "completed"]
          /\ UNCHANGED <<inventory, orders, orderStatus, reservations, processing, timestamp>>
       \/ /\ payments' = [payments EXCEPT ![orderIndex] = "failed"]
          /\ \* CLEAR POLICY: Failed payment triggers automatic cancellation
             IF orderStatus[orderIndex] \in {"reserved", "confirmed"}
             THEN LET order == orders[orderIndex] IN
                  /\ inventory' = [inventory EXCEPT 
                      ![order.book].physicalStock = @ + order.quantity,
                      ![order.book].reservedStock = @ - order.quantity]
                  /\ orderStatus' = [orderStatus EXCEPT ![orderIndex] = "cancelled"]
                  /\ reservations' = [reservations EXCEPT ![orderIndex] = "released"]
                  /\ processing' = processing \ {orderIndex}
             ELSE UNCHANGED <<inventory, orderStatus, reservations, processing>>
          /\ timestamp' = timestamp + 1
          /\ UNCHANGED orders

\* RESOLVED AMBIGUITY 4: Clear cancellation rules
\* SOLUTION: Only pending/reserved orders can be cancelled, not confirmed/shipped
CancelOrder(orderIndex) ==
    /\ orderIndex \in 1..Len(orders)
    /\ orderStatus[orderIndex] \in {"pending", "reserved"} \* CLEAR RULE: No cancellation after confirmation
    /\ LET order == orders[orderIndex] IN
        /\ IF orderStatus[orderIndex] = "reserved"
           THEN \* Restore inventory for reserved orders
                /\ inventory' = [inventory EXCEPT 
                    ![order.book].physicalStock = @ + order.quantity,
                    ![order.book].reservedStock = @ - order.quantity]
                /\ reservations' = [reservations EXCEPT ![orderIndex] = "released"]
           ELSE /\ UNCHANGED inventory
                /\ reservations' = [reservations EXCEPT ![orderIndex] = "released"]
        /\ orderStatus' = [orderStatus EXCEPT ![orderIndex] = "cancelled"]
        /\ processing' = processing \ {orderIndex}
        /\ timestamp' = timestamp + 1
        /\ UNCHANGED <<orders, payments>>

\* RESOLVED AMBIGUITY 5: Shipping requires completed payment
\* SOLUTION: Strict payment-before-shipping policy
ShipOrder(orderIndex) ==
    /\ orderIndex \in 1..Len(orders)
    /\ orderStatus[orderIndex] = "confirmed"
    /\ payments[orderIndex] = "completed" \* STRICT REQUIREMENT: Payment must be completed
    /\ orderIndex \in processing
    /\ orderStatus' = [orderStatus EXCEPT ![orderIndex] = "shipped"]
    /\ processing' = processing \ {orderIndex}
    /\ timestamp' = timestamp + 1
    /\ UNCHANGED <<inventory, orders, payments, reservations>>

\* RESOLVED AMBIGUITY 6: Timeout handling for reservations
\* SOLUTION: Automatic release of expired reservations
ReleaseExpiredReservation(orderIndex) ==
    /\ orderIndex \in 1..Len(orders)
    /\ orderStatus[orderIndex] = "reserved"
    /\ reservations[orderIndex] = "reserved"
    /\ timestamp > 8 \* Timeout: 8 time units (reduced for performance)
    /\ LET order == orders[orderIndex] IN
        /\ inventory' = [inventory EXCEPT 
            ![order.book].physicalStock = @ + order.quantity,
            ![order.book].reservedStock = @ - order.quantity]
        /\ orderStatus' = [orderStatus EXCEPT ![orderIndex] = "cancelled"]
        /\ reservations' = [reservations EXCEPT ![orderIndex] = "expired"]
        /\ timestamp' = timestamp + 1
        /\ UNCHANGED <<orders, payments, processing>>

\* Next state relation
Next ==
    \/ \E c \in Customers, b \in Books, q \in 1..MaxStock: PlaceOrderWithReservation(c, b, q)
    \/ \E i \in 1..Len(orders): ConfirmReservedOrder(i)
    \/ \E i \in 1..Len(orders): ProcessPayment(i)
    \/ \E i \in 1..Len(orders): CancelOrder(i)
    \/ \E i \in 1..Len(orders): ShipOrder(i)
    \/ \E i \in 1..Len(orders): ReleaseExpiredReservation(i)
    \/ UNCHANGED <<inventory, orders, orderStatus, payments, reservations, processing, timestamp>>

\* Specification
Spec == Init /\ [][Next]_<<inventory, orders, orderStatus, payments, reservations, processing, timestamp>>

\* SAFETY PROPERTIES (these should now hold)

\* Property 1: Inventory should never go negative
InventoryNeverNegative ==
    \A b \in Books: inventory[b].physicalStock >= 0

\* Property 2: Reserved stock should never exceed total stock
ReservedStockConsistency ==
    \A b \in Books: inventory[b].reservedStock <= MaxStock

\* Property 3: Physical + Reserved stock should equal MaxStock (conservation)
StockConservation ==
    \A b \in Books: inventory[b].physicalStock + inventory[b].reservedStock = MaxStock

\* Property 4: No overbooking - reserved stock matches active reservations
NoOverbooking ==
    \A b \in Books:
        LET activeReservations == 
            {i \in 1..Len(orders) : 
             orders[i].book = b /\ 
             orderStatus[i] \in {"reserved", "confirmed", "shipped"} /\
             reservations[i] \in {"reserved"}} IN
        LET totalReserved == 
            IF activeReservations = {} THEN 0
            ELSE LET SumQuantities[S \in SUBSET activeReservations] ==
                     IF S = {} THEN 0
                     ELSE LET i == CHOOSE x \in S : TRUE IN
                          orders[i].quantity + SumQuantities[S \ {i}]
                 IN SumQuantities[activeReservations]
        IN totalReserved = inventory[b].reservedStock

\* Property 5: Confirmed orders must have completed payments before shipping
PaymentBeforeShipping ==
    \A i \in 1..Len(orders):
        orderStatus[i] = "shipped" => payments[i] = "completed"

\* Property 6: Mutual exclusion - only one order per book in processing
MutualExclusion ==
    \A b \in Books:
        Cardinality({i \in processing : orders[i].book = b}) <= 1

\* Property 7: State consistency - order status matches reservation status
StateConsistency ==
    \A i \in 1..Len(orders):
        /\ (orderStatus[i] = "reserved" => reservations[i] = "reserved")
        /\ (orderStatus[i] = "cancelled" => reservations[i] \in {"released", "expired"})
        /\ (orderStatus[i] \in {"confirmed", "shipped"} => reservations[i] = "reserved")

==== 