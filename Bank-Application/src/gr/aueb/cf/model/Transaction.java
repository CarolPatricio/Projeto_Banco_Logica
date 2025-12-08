package gr.aueb.cf.model;

/**
 * The {@code Transaction} class represents a bank transaction.
 * Refactored: Removed date and description for simplified verification.
 *
 * @author Bank Application
 */
public class Transaction {
    public enum TransactionType {
        DEPOSIT,
        WITHDRAWAL,
        TRANSFER_OUT,
        TRANSFER_IN,
        LOAN_REQUEST,
        LOAN_REPAYMENT,
        CARD_PURCHASE,
        BILL_PAYMENT
    }

    //@ spec_public nullable
    private TransactionType type;
    
    //@ spec_public
    private double amount;
    
    //@ spec_public
    private double balanceAfter;

    //@ public invariant amount >= 0;

    /**
     * Constructor for creating a transaction.
     * * @param type the type of transaction
     * @param amount the amount involved
     * @param balanceAfter the account balance after the transaction
     */
    //@ requires amount >= 0;
    //@ ensures this.type == type;
    //@ ensures this.amount == amount;
    //@ ensures this.balanceAfter == balanceAfter;
    //@ pure 
    public Transaction(TransactionType type, double amount, double balanceAfter) {
        this.type = type;
        this.amount = amount;
        this.balanceAfter = balanceAfter;
    }

    // Getters

    //@ ensures \result == type;
    public /*@ pure nullable @*/ TransactionType getType() {
        return type;
    }

    //@ ensures \result == amount;
    public /*@ pure @*/ double getAmount() {
        return amount;
    }

    //@ ensures \result == balanceAfter;
    public /*@ pure @*/ double getBalanceAfter() {
        return balanceAfter;
    }

    /**
     * Returns a formatted string representation of the transaction.
     *
     * @return formatted transaction string
     */
    @Override
    public /*@ pure skipesc @*/ String toString() {
        String sign = (type == TransactionType.DEPOSIT || 
                       type == TransactionType.TRANSFER_IN || 
                       type == TransactionType.LOAN_REQUEST) ? "+" : "-";
        
        String typeStr = (type != null) ? type.name() : "UNKNOWN";
        
        return String.format("[%s] %s%.2f | Balance: %.2f",
                typeStr,
                sign,
                amount,
                balanceAfter);
    }
}