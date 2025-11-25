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

    private TransactionType type;
    private double amount;
    private LocalDateTime date;
    private String description;
    private double balanceAfter;

    /**
     * Constructor for creating a transaction.
     *
     * @param type the type of transaction
     * @param amount the amount involved
     * @param description description of the transaction
     * @param balanceAfter the account balance after the transaction
     */
    public Transaction(TransactionType type, double amount, String description, double balanceAfter) {
        this.type = type;
        this.amount = amount;
        this.description = description;
        this.balanceAfter = balanceAfter;
        this.date = LocalDateTime.now();
    }

    // Getters
    public TransactionType getType() {
        return type;
    }

    public double getAmount() {
        return amount;
    }

    public LocalDateTime getDate() {
        return date;
    }

    public String getDescription() {
        return description;
    }

    public double getBalanceAfter() {
        return balanceAfter;
    }

    /**
     * Returns a formatted string representation of the transaction.
     *
     * @return formatted transaction string
     */
    @Override
    public String toString() {
        DateTimeFormatter formatter = DateTimeFormatter.ofPattern("yyyy-MM-dd HH:mm:ss");
        String sign = (type == TransactionType.DEPOSIT || 
                       type == TransactionType.TRANSFER_IN || 
                       type == TransactionType.LOAN_REQUEST) ? "+" : "-";
        return String.format("[%s] %s %s%.2f | %s | Balance: %.2f",
                date.format(formatter),
                type.name(),
                sign,
                amount,
                description,
                balanceAfter);
    }
}

