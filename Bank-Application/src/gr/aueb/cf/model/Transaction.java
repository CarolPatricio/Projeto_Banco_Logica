package gr.aueb.cf.model;

import java.time.LocalDateTime;
import java.time.format.DateTimeFormatter;

/**
 * The {@code Transaction} class represents a bank transaction.
 * It stores information about the transaction type, amount, date, and description.
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
    
    //@ spec_public nullable
    private LocalDateTime date;
    
    //@ spec_public nullable
    private String description;
    
    //@ spec_public
    private double balanceAfter;

    //@ public invariant amount >= 0;

    /**
     * Constructor for creating a transaction.
     *
     * @param type the type of transaction
     * @param amount the amount involved
     * @param description description of the transaction
     * @param balanceAfter the account balance after the transaction
     */
    //@ skipesc
    public Transaction(TransactionType type, double amount, String description, double balanceAfter) {
        this.type = type;
        this.amount = amount;
        this.description = description;
        this.balanceAfter = balanceAfter;
        this.date = LocalDateTime.now();
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

    //@ ensures \result == date;
    public /*@ pure nullable @*/ LocalDateTime getDate() {
        return date;
    }

    //@ ensures \result == description;
    public /*@ pure nullable @*/ String getDescription() {
        return description;
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
    //@ skipesc
    @Override
    public String toString() {
        DateTimeFormatter formatter = DateTimeFormatter.ofPattern("yyyy-MM-dd HH:mm:ss");
        String sign = (type == TransactionType.DEPOSIT || 
                       type == TransactionType.TRANSFER_IN || 
                       type == TransactionType.LOAN_REQUEST) ? "+" : "-";
        String dateStr = (date != null) ? date.format(formatter) : "N/A";
        String typeStr = (type != null) ? type.name() : "UNKNOWN";
        
        return String.format("[%s] %s %s%.2f | %s | Balance: %.2f",
                dateStr,
                typeStr,
                sign,
                amount,
                description,
                balanceAfter);
    }
}