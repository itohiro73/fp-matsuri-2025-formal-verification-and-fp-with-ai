---- MODULE BookstoreSystem ----
\* Bookstore System - TLA+ Specification
\* This specification reveals ambiguities in concurrent behavior and state transitions

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
    processing,     \* Set of orders currently being processed
    timestamp       \* Current logical timestamp

\* Order and payment status definitions
OrderStatuses == {"pending", "confirmed", "shipped", "cancelled"}
PaymentStatuses == {"pending", "completed", "failed"}

\* Type invariant
TypeInvariant ==
    /\ inventory \in [Books -> [physicalStock: Nat, reservedStock: Nat]]
    /\ orders \in Seq([customer: Customers, book: Books, quantity: Nat])
    /\ orderStatus \in [1..Len(orders) -> OrderStatuses]
    /\ payments \in [1..Len(orders) -> PaymentStatuses]
    /\ processing \subseteq 1..Len(orders)
    /\ timestamp \in Nat

\* Initial state
Init ==
    /\ inventory = [b \in Books |-> [physicalStock |-> MaxStock, reservedStock |-> 0]]
    /\ orders = <<>>
    /\ orderStatus = <<>>
    /\ payments = <<>>
    /\ processing = {}
    /\ timestamp = 0

\* AMBIGUITY REVELATION: Order placement timing
\* PROBLEM: When exactly is stock checked and reserved?
PlaceOrder(customer, book, quantity) ==
    /\ quantity > 0
    /\ quantity <= MaxStock
    /\ Len(orders) < MaxOrders
    \* AMBIGUITY: Should we check stock availability here?
    \* Current spec doesn't check - this allows overbooking!
    /\ orders' = Append(orders, [customer |-> customer, book |-> book, quantity |-> quantity])
    /\ orderStatus' = Append(orderStatus, "pending")
    /\ payments' = Append(payments, "pending")
    /\ timestamp' = timestamp + 1
    /\ UNCHANGED <<inventory, processing>>

\* AMBIGUITY REVELATION: Stock reservation timing
\* PROBLEM: Multiple orders can be confirmed simultaneously
ConfirmOrder(orderIndex) ==
    /\ orderIndex \in 1..Len(orders)
    /\ orderStatus[orderIndex] = "pending"
    /\ orderIndex \notin processing
    /\ LET order == orders[orderIndex] IN
        \* RACE CONDITION: Check and update are not atomic!
        /\ inventory[order.book].physicalStock >= order.quantity
        /\ inventory' = [inventory EXCEPT 
            ![order.book].physicalStock = @ - order.quantity,
            ![order.book].reservedStock = @ + order.quantity]
        /\ orderStatus' = [orderStatus EXCEPT ![orderIndex] = "confirmed"]
        /\ processing' = processing \cup {orderIndex}
        /\ timestamp' = timestamp + 1
        /\ UNCHANGED <<orders, payments>>

\* AMBIGUITY REVELATION: Payment processing timing
\* PROBLEM: When does payment happen relative to confirmation?
ProcessPayment(orderIndex) ==
    /\ orderIndex \in 1..Len(orders)
    /\ payments[orderIndex] = "pending"
    /\ \/ /\ payments' = [payments EXCEPT ![orderIndex] = "completed"]
          /\ UNCHANGED <<inventory, orders, orderStatus, processing, timestamp>>
       \/ /\ payments' = [payments EXCEPT ![orderIndex] = "failed"]
          /\ \* AMBIGUITY: What happens to confirmed orders with failed payments?
             IF orderStatus[orderIndex] = "confirmed"
             THEN LET order == orders[orderIndex] IN
                  /\ inventory' = [inventory EXCEPT 
                      ![order.book].physicalStock = @ + order.quantity,
                      ![order.book].reservedStock = @ - order.quantity]
                  /\ orderStatus' = [orderStatus EXCEPT ![orderIndex] = "cancelled"]
                  /\ processing' = processing \ {orderIndex}
             ELSE UNCHANGED <<inventory, orderStatus, processing>>
          /\ timestamp' = timestamp + 1
          /\ UNCHANGED orders

\* AMBIGUITY REVELATION: Cancellation rules
\* PROBLEM: Can any status be cancelled? What about shipped orders?
CancelOrder(orderIndex) ==
    /\ orderIndex \in 1..Len(orders)
    /\ orderStatus[orderIndex] \in {"pending", "confirmed"} \* AMBIGUITY: What about "shipped"?
    /\ LET order == orders[orderIndex] IN
        /\ IF orderStatus[orderIndex] = "confirmed"
           THEN \* Restore inventory
                inventory' = [inventory EXCEPT 
                    ![order.book].physicalStock = @ + order.quantity,
                    ![order.book].reservedStock = @ - order.quantity]
           ELSE UNCHANGED inventory
        /\ orderStatus' = [orderStatus EXCEPT ![orderIndex] = "cancelled"]
        /\ processing' = processing \ {orderIndex}
        /\ timestamp' = timestamp + 1
        /\ UNCHANGED <<orders, payments>>

\* AMBIGUITY REVELATION: Shipping conditions
\* PROBLEM: Can orders be shipped without payment completion?
ShipOrder(orderIndex) ==
    /\ orderIndex \in 1..Len(orders)
    /\ orderStatus[orderIndex] = "confirmed"
    /\ payments[orderIndex] = "completed" \* ASSUMPTION: Payment must be completed
    /\ orderStatus' = [orderStatus EXCEPT ![orderIndex] = "shipped"]
    /\ processing' = processing \ {orderIndex}
    /\ timestamp' = timestamp + 1
    /\ UNCHANGED <<inventory, orders, payments>>

\* Next state relation
Next ==
    \/ \E c \in Customers, b \in Books, q \in 1..MaxStock: PlaceOrder(c, b, q)
    \/ \E i \in 1..Len(orders): ConfirmOrder(i)
    \/ \E i \in 1..Len(orders): ProcessPayment(i)
    \/ \E i \in 1..Len(orders): CancelOrder(i)
    \/ \E i \in 1..Len(orders): ShipOrder(i)
    \/ UNCHANGED <<inventory, orders, orderStatus, payments, processing, timestamp>>

\* Specification
Spec == Init /\ [][Next]_<<inventory, orders, orderStatus, payments, processing, timestamp>>

\* SAFETY PROPERTIES (these will likely be violated, revealing problems)

\* Property 1: Inventory should never go negative
InventoryNeverNegative ==
    \A b \in Books: inventory[b].physicalStock >= 0

\* Property 2: Reserved stock should never exceed physical stock
ReservedStockConsistency ==
    \A b \in Books: inventory[b].reservedStock <= inventory[b].physicalStock

\* Property 3: No overbooking - total confirmed orders shouldn't exceed initial stock
NoOverbooking ==
    \A b \in Books:
        LET confirmedOrders == {i \in 1..Len(orders) : 
                                orders[i].book = b /\ orderStatus[i] \in {"confirmed", "shipped"}} IN
        LET totalConfirmed == IF confirmedOrders = {} 
                             THEN 0 
                             ELSE LET sum[S \in SUBSET (1..Len(orders))] ==
                                      IF S = {} THEN 0
                                      ELSE LET i == CHOOSE x \in S : TRUE IN
                                           orders[i].quantity + sum[S \ {i}]
                                  IN sum[confirmedOrders] IN
        totalConfirmed <= MaxStock

\* Property 4: Confirmed orders must have completed payments (eventually)
ConfirmedOrdersHavePayments ==
    \A i \in 1..Len(orders):
        orderStatus[i] = "confirmed" => payments[i] = "completed"

\* Property 5: Shipped orders must be confirmed first
ShippedOrdersWereConfirmed ==
    \A i \in 1..Len(orders):
        orderStatus[i] = "shipped" => payments[i] = "completed"

\* LIVENESS PROPERTIES (these reveal timing ambiguities)

\* Property 6: Pending orders should eventually be processed
OrdersEventuallyProcessed ==
    \A i \in 1..Len(orders):
        orderStatus[i] = "pending" ~> orderStatus[i] \in {"confirmed", "cancelled"}

\* Property 7: Confirmed orders should eventually be shipped or cancelled
ConfirmedOrdersEventuallyShipped ==
    \A i \in 1..Len(orders):
        orderStatus[i] = "confirmed" ~> orderStatus[i] \in {"shipped", "cancelled"}

\* Property 8: Payment processing should complete
PaymentsEventuallyProcessed ==
    \A i \in 1..Len(orders):
        payments[i] = "pending" ~> payments[i] \in {"completed", "failed"}

\* PROBLEMATIC SCENARIOS TO EXPLORE

\* Scenario 1: Race condition - two orders for the same book
RaceCondition ==
    /\ Len(orders) >= 2
    /\ \E i, j \in 1..Len(orders):
        /\ i # j
        /\ orders[i].book = orders[j].book
        /\ orderStatus[i] = "pending"
        /\ orderStatus[j] = "pending"
        /\ orders[i].quantity + orders[j].quantity > MaxStock

\* Scenario 2: Payment failure after confirmation
PaymentFailureAfterConfirmation ==
    /\ \E i \in 1..Len(orders):
        /\ orderStatus[i] = "confirmed"
        /\ payments[i] = "failed"

\* Scenario 3: Inconsistent inventory state
InconsistentInventory ==
    /\ \E b \in Books:
        inventory[b].reservedStock > inventory[b].physicalStock

\* TEMPORAL PROPERTIES TO CHECK

\* Mutual exclusion: Only one order can be processed at a time for the same book
MutualExclusion ==
    \A b \in Books:
        Cardinality({i \in processing : orders[i].book = b}) <= 1

\* Progress: If there's available stock, pending orders should eventually be confirmed
StockAvailableImpliesProgress ==
    \A i \in 1..Len(orders):
        /\ orderStatus[i] = "pending"
        /\ inventory[orders[i].book].physicalStock >= orders[i].quantity
        ~> orderStatus[i] = "confirmed"

==== 