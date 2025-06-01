// Main entry point for legacy expense application
import { ExpenseForm } from './expense-form';
import { StateManager } from './state-management';
import { ApprovalLogic } from './approval-logic';

console.log('Legacy Expense Application - Demo Build');
console.log('This is a demo application showing problematic patterns');

// Initialize demo components (for build verification)
const stateManager = new StateManager();
const approvalLogic = new ApprovalLogic();
const expenseForm = new ExpenseForm();

export { ExpenseForm, StateManager, ApprovalLogic };