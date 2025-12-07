package gr.aueb.cf.model;

import gr.aueb.cf.exceptions.InsufficientAmountException;
import gr.aueb.cf.exceptions.InsufficientBalanceException;
import gr.aueb.cf.exceptions.SsnNotValidException;
import gr.aueb.cf.exceptions.InsufficientCreditException;
import java.time.LocalDateTime;

import java.util.ArrayList;
import java.util.List;

/**
 * The {@code Account} class represents a bank account belonging to a user,
 * identified by a unique International Bank Account Number (IBAN).
 * It provides methods for depositing and withdrawing money from the account.
 *
 * @author Ntirintis John
 */
public class Account extends IdentifiableEntity {

    //@ spec_public
    //@ nullable
    private User holder;
    //@ spec_public
    //@ non_null
    private String iban;
    //@ spec_public
    private double balance;
    //@ spec_public
    private double loanBalance;
    //@ spec_public
    private double creditLimit;
    //@ spec_public
    private double interestRate;
    //@ spec_public
    private boolean isActive;
    //@ spec_public nullable
    private List<Transaction> transactionHistory = new ArrayList<>();;

    //@ public invariant holder != null;
    //@ public invariant iban != null;
    //@ public invariant transactionHistory != null;

    //@ requires holder != null;
    //@ requires iban != null;
    //@ requires balance >= 0;
    //@ ensures this.holder == holder;
    //@ ensures this.iban == iban;
    //@ ensures this.balance == balance;
    //@ ensures this.loanBalance == 0;
    //@ ensures this.creditLimit == 10000.0;
    //@ ensures this.interestRate == 0.05;
    //@ ensures this.isActive == true;
    //@ ensures this.transactionHistory != null;
    public Account(User holder, String iban, double balance) {
        this.holder = holder;
        this.iban = iban;
        this.balance = balance;
        this.loanBalance = 0;
        this.creditLimit = 10000.0; 
        this.interestRate = 0.05; 
        this.isActive = true;
        if (balance > 0) {
            addTransaction(Transaction.TransactionType.DEPOSIT, balance, "Initial deposit", balance);
        }
    }

    // Getters / Setters
    //@ ensures \result != null;
    //@ pure
    public User getHolder() {
        return holder;
    }

    //@ requires holder != null;
    //@ assignable this.holder;
    //@ ensures this.holder == holder;
    public void setHolder(User holder) {
        this.holder = holder;
    }

    //@ ensures \result != null; 
    //@ pure
    public String getIban() {
        return iban;
    }

    //@ requires iban != null;
    //@ assignable this.iban;
    public void setIban(String iban) {
        this.iban = iban;
    }

    //@ pure
    public double getBalance() {
        return balance;
    }

    //@ assignable this.balance;
    public void setBalance(double balance) {
        this.balance = balance;
    }

    //@ pure
    public double getLoanBalance() {
        return loanBalance;
    }

    //@ assignable this.loanBalance;
    public void setLoanBalance(double loanBalance) {
        this.loanBalance = loanBalance;
    }

    //@ pure
    public double getCreditLimit() {
        return creditLimit;
    }

    //@ requires creditLimit >= 0;
    //@ assignable this.creditLimit;
    public void setCreditLimit(double creditLimit) {
        this.creditLimit = creditLimit;
    }

    //@ pure
    public double getInterestRate() {
        return interestRate;
    }

    //@ requires interestRate >= 0;
    //@ assignable this.interestRate;
    public void setInterestRate(double interestRate) {
        this.interestRate = interestRate;
    }

    //@ pure
    public boolean isActive() {
        return isActive;
    }

    //@ pure
    public List<Transaction> getTransactionHistory() {
        return new ArrayList<>(transactionHistory);
    }

    //@ skipesc
    @Override
    public String toString() {
        return "Account{" +
                "holder=" + holder.toString() +
                ", iban='" + iban + '\'' +
                ", balance=" + balance +
                ", loanBalance=" + loanBalance +
                ", creditLimit=" + creditLimit +
                ", interestRate=" + (interestRate * 100) + "%" +
                ", isActive=" + isActive +
                '}';
    }

    // Public API

    /**
    * Deposits a given amount to the bank account
    *
    * @param amount amount to be deposited
    * @throws InsufficientAmountException if amount is zero or negative
    * @throws IllegalStateException if account is closed
    */
    //@ public normal_behavior
    //@   requires amount > 0;
    //@   requires isActive;
    //@   requires holder != null;
    //@   requires iban != null;
    //@   requires transactionHistory != null;
    //@   requires id >= 0;                  // se IdentifiableEntity exige id >= 0
    //@   assignable balance, transactionHistory, transactionHistory.*;
    //@   ensures balance == \old(balance) + amount;
    //@ also
    //@ public exceptional_behavior
    //@   requires amount <= 0;
    //@   requires holder != null;
    //@   requires iban != null;
    //@   requires transactionHistory != null;
    //@   requires id >= 0;
    //@   signals (InsufficientAmountException e) amount <= 0;
    //@ also
    //@ public exceptional_behavior
    //@   requires !isActive;
    //@   requires holder != null;
    //@   requires iban != null;
    //@   requires transactionHistory != null;
    //@   requires id >= 0;
    //@   signals (IllegalStateException e) !isActive;
    public void deposit(double amount) throws InsufficientAmountException {
        if (!isActive) {
            throw new IllegalStateException("Cannot perform operations on a closed account.");
        }
        if(amount <= 0){
            throw new InsufficientAmountException(amount);
        }
        balance += amount;
        addTransaction(Transaction.TransactionType.DEPOSIT, amount, "Deposit", balance);
    }

    /**
     * Withdraws a given amount from the bank account if the holder's social security number (SSN)
     * matches the one given and the balance is sufficient.
     *
     * @param amount the amount to be withdrawn
     * @param ssn the social security number of the account holder
     * @throws InsufficientBalanceException if the amount is greater than the current balance
     * @throws SsnNotValidException if the social security number doesn't match the holder's SSN
     * @throws InsufficientAmountException if the amount is zero or negative
     * @throws IllegalStateException if account is closed
     */
    public void withdraw(double amount, String ssn)
            throws InsufficientBalanceException, SsnNotValidException, InsufficientAmountException {
        if (!isActive) {
            throw new IllegalStateException("Cannot perform operations on a closed account.");
        }
        try {
            if(amount <= 0) throw new InsufficientAmountException(amount);
            if(amount > balance) throw new InsufficientBalanceException(getBalance(), amount);
            if(!isSsnValid(ssn)) throw new SsnNotValidException(ssn);

            balance -= amount;
            addTransaction(Transaction.TransactionType.WITHDRAWAL, amount, "Withdrawal", balance);

        } catch (InsufficientAmountException | InsufficientBalanceException | SsnNotValidException e){
            // Would be better to have more catch statements and have exception specific err messages
            System.err.println("Error: Withdrawal");
            throw e;
        }
    }


    /**
     * Requests a loan of a given amount.
     * The amount is added to the account balance and the loan balance.
     * Validates credit limit and eligibility before approving the loan.
     *
     * @param amount the amount of the loan
     * @throws InsufficientAmountException if the amount is zero or negative
     * @throws InsufficientCreditException if the loan amount exceeds the credit limit or available credit
     */
    public void requestLoan(double amount) throws InsufficientAmountException, InsufficientCreditException {
        if (amount <= 0) throw new InsufficientAmountException(amount);
        
        // Check if loan amount exceeds credit limit
        if (amount > creditLimit) {
            throw new InsufficientCreditException(creditLimit, amount);
        }
        
        // Check if total loan balance would exceed credit limit
        if (loanBalance + amount > creditLimit) {
            double availableCredit = creditLimit - loanBalance;
            throw new InsufficientCreditException(availableCredit, amount);
        }
        
        // Approve loan: add to balance and loan balance
        balance += amount;
        loanBalance += amount;
        addTransaction(Transaction.TransactionType.LOAN_REQUEST, amount, "Loan request", balance);
    }

    /**
     * Calculates the interest amount for the current loan balance.
     * Interest is calculated based on the annual interest rate.
     *
     * @param months number of months to calculate interest for
     * @return the interest amount
     */
    public double calculateInterest(int months) {
        if (loanBalance <= 0) return 0.0;
        // Simple interest calculation: principal * rate * time
        return loanBalance * interestRate * (months / 12.0);
    }

    /**
     * Calculates the total amount to repay including interest.
     *
     * @param months number of months for the loan term
     * @return total amount (principal + interest)
     */
    public double calculateTotalLoanAmount(int months) {
        return loanBalance + calculateInterest(months);
    }

    /**
     * Checks if the account is eligible for a loan.
     * An account is eligible if it has available credit.
     *
     * @return true if eligible, false otherwise
     */
    public boolean isEligibleForLoan() {
        return loanBalance < creditLimit;
    }

    /**
     * Gets the available credit (credit limit minus current loan balance).
     *
     * @return available credit amount
     */
    public double getAvailableCredit() {
        return Math.max(0, creditLimit - loanBalance);
    }

    /**
     * Repays a portion of the loan.
     *
     * @param amount the amount to repay
     * @throws InsufficientAmountException if the amount is zero or negative
     * @throws InsufficientBalanceException if the account balance is insufficient
     * @throws IllegalArgumentException if the repayment amount exceeds the loan balance
     */
    public void repayLoan(double amount) throws InsufficientAmountException, InsufficientBalanceException {
        if (amount <= 0) throw new InsufficientAmountException(amount);
        if (amount > balance) throw new InsufficientBalanceException(balance, amount);
        if (amount > loanBalance) throw new IllegalArgumentException("Repayment amount exceeds loan balance.");

        balance -= amount;
        loanBalance -= amount;
        addTransaction(Transaction.TransactionType.LOAN_REPAYMENT, amount, "Loan repayment", balance);
    }

    /**
     * Transfers a given amount from this account to another account.
     * For regular accounts, the balance must be sufficient. For overdraft accounts,
     * the balance can go negative.
     *
     * @param amount the amount to be transferred
     * @param ssn the social security number of the account holder (sender)
     * @param destinationAccount the account to receive the transfer
     * @throws InsufficientAmountException if the amount is zero or negative
     * @throws InsufficientBalanceException if the amount is greater than the current balance (only for regular accounts)
     * @throws SsnNotValidException if the social security number doesn't match the holder's SSN
     * @throws IllegalArgumentException if the destination account is null or the same as the source account
     */
    public void transfer(double amount, String ssn, Account destinationAccount)
            throws InsufficientAmountException, InsufficientBalanceException, SsnNotValidException {
        try {
            // Validar valor
            if (amount <= 0) throw new InsufficientAmountException(amount);
            
            // Validar conta destino
            if (destinationAccount == null) {
                throw new IllegalArgumentException("Destination account cannot be null.");
            }
            
            // Validar que não está transferindo para a mesma conta
            if (this.equals(destinationAccount)) {
                throw new IllegalArgumentException("Cannot transfer to the same account.");
            }
            
            // Validar SSN
            if (!isSsnValid(ssn)) throw new SsnNotValidException(ssn);
            
            // Verificar saldo (apenas para contas normais, não para overdraft)
            // Se for OverdraftAccount, não precisa verificar saldo
            if (!(this instanceof OverdraftAccount) && amount > balance) {
                throw new InsufficientBalanceException(getBalance(), amount);
            }
            
            // Realizar transferência: debitar da conta origem
            balance -= amount;
            addTransaction(Transaction.TransactionType.TRANSFER_OUT, amount, 
                    "Transfer to " + destinationAccount.getIban(), balance);
            
            // Creditar na conta destino
            destinationAccount.balance += amount;
            destinationAccount.addTransaction(Transaction.TransactionType.TRANSFER_IN, amount,
                    "Transfer from " + this.iban, destinationAccount.getBalance());
            
        } catch (InsufficientAmountException | InsufficientBalanceException | SsnNotValidException e) {
            System.err.println("Error: Transfer failed");
            throw e;
        }
    }

    /**
     * Checks if a given social security number (SSN) is the same as the account holder's.
     *
     * @param ssn the social security number to be checked
     * @return true if the given SSN matches the holder's, false otherwise
     */
    protected boolean isSsnValid(String ssn){
        if(ssn == null || getHolder().getSsn() == null) return false;

        // We dont use getHolder because we are in the same class
        return holder.getSsn().equals(ssn);
    }

    /**
     * Closes the account. An account can only be closed if:
     * - The balance is zero (or positive)
     * - There are no outstanding loans
     *
     * @param ssn the social security number of the account holder
     * @throws SsnNotValidException if the SSN is not valid
     * @throws IllegalStateException if the account cannot be closed (has balance or loans)
     */
    public void closeAccount(String ssn) throws SsnNotValidException, IllegalStateException {
        if (!isSsnValid(ssn)) {
            throw new SsnNotValidException(ssn);
        }
        
        if (!isActive) {
            throw new IllegalStateException("Account is already closed.");
        }
        
        if (balance < 0) {
            throw new IllegalStateException("Cannot close account with negative balance.");
        }
        
        if (loanBalance > 0) {
            throw new IllegalStateException("Cannot close account with outstanding loan balance: " + loanBalance);
        }
        
        // If balance > 0, it should be withdrawn first, but we'll allow closing with zero balance
        if (balance > 0) {
            throw new IllegalStateException("Cannot close account with remaining balance. Please withdraw " + balance + " first.");
        }
        
        isActive = false;
        addTransaction(Transaction.TransactionType.WITHDRAWAL, 0, "Account closed", balance);
    }

    /**
     * Updates the account holder's first name.
     *
     * @param newFirstName the new first name
     * @param ssn the social security number for verification
     * @throws SsnNotValidException if the SSN is not valid
     * @throws IllegalStateException if account is closed
     */
    public void updateHolderFirstName(String newFirstName, String ssn) throws SsnNotValidException {
        if (!isActive) {
            throw new IllegalStateException("Cannot update data on a closed account.");
        }
        if (!isSsnValid(ssn)) {
            throw new SsnNotValidException(ssn);
        }
        holder.setFirstName(newFirstName);
    }

    /**
     * Updates the account holder's last name.
     *
     * @param newLastName the new last name
     * @param ssn the social security number for verification
     * @throws SsnNotValidException if the SSN is not valid
     * @throws IllegalStateException if account is closed
     */
    public void updateHolderLastName(String newLastName, String ssn) throws SsnNotValidException {
        if (!isActive) {
            throw new IllegalStateException("Cannot update data on a closed account.");
        }
        if (!isSsnValid(ssn)) {
            throw new SsnNotValidException(ssn);
        }
        holder.setLastName(newLastName);
    }

    /**
     * Updates the account holder's full name.
     *
     * @param newFirstName the new first name
     * @param newLastName the new last name
     * @param ssn the social security number for verification
     * @throws SsnNotValidException if the SSN is not valid
     * @throws IllegalStateException if account is closed
     */
    public void updateHolderName(String newFirstName, String newLastName, String ssn) throws SsnNotValidException {
        if (!isActive) {
            throw new IllegalStateException("Cannot update data on a closed account.");
        }
        if (!isSsnValid(ssn)) {
            throw new SsnNotValidException(ssn);
        }
        holder.setFirstName(newFirstName);
        holder.setLastName(newLastName);
    }

    /**
     * Generates a statement (extract) of the account showing all transactions.
     *
     * @return a formatted string containing the account statement
     */
    public String generateStatement() {
        StringBuilder statement = new StringBuilder();
        statement.append("========================================\n");
        statement.append("ACCOUNT STATEMENT\n");
        statement.append("========================================\n");
        statement.append("IBAN: ").append(iban).append("\n");
        statement.append("Holder: ").append(holder.getFirstName()).append(" ").append(holder.getLastName()).append("\n");
        statement.append("SSN: ").append(holder.getSsn()).append("\n");
        statement.append("Status: ").append(isActive ? "ACTIVE" : "CLOSED").append("\n");
        statement.append("Current Balance: ").append(String.format("%.2f", balance)).append("\n");
        statement.append("Loan Balance: ").append(String.format("%.2f", loanBalance)).append("\n");
        statement.append("Credit Limit: ").append(String.format("%.2f", creditLimit)).append("\n");
        statement.append("========================================\n");
        statement.append("TRANSACTION HISTORY\n");
        statement.append("========================================\n");
        
        if (transactionHistory.isEmpty()) {
            statement.append("No transactions recorded.\n");
        } else {
            for (Transaction transaction : transactionHistory) {
                statement.append(transaction.toString()).append("\n");
            }
        }
        
        statement.append("========================================\n");
        statement.append("Total Transactions: ").append(transactionHistory.size()).append("\n");
        statement.append("========================================\n");
        
        return statement.toString();
    }

    /**
     * Generates a statement for a specific date range.
     *
     * @param startDate the start date (inclusive)
     * @param endDate the end date (inclusive)
     * @return a formatted string containing the filtered statement
     */
    public String generateStatement(java.time.LocalDateTime startDate, java.time.LocalDateTime endDate) {
        StringBuilder statement = new StringBuilder();
        statement.append("========================================\n");
        statement.append("ACCOUNT STATEMENT (FILTERED)\n");
        statement.append("========================================\n");
        statement.append("IBAN: ").append(iban).append("\n");
        statement.append("Holder: ").append(holder.getFirstName()).append(" ").append(holder.getLastName()).append("\n");
        statement.append("Period: ").append(startDate.toString()).append(" to ").append(endDate.toString()).append("\n");
        statement.append("Current Balance: ").append(String.format("%.2f", balance)).append("\n");
        statement.append("========================================\n");
        statement.append("TRANSACTION HISTORY\n");
        statement.append("========================================\n");
        
        int count = 0;
        for (Transaction transaction : transactionHistory) {
            if (!transaction.getDate().isBefore(startDate) && !transaction.getDate().isAfter(endDate)) {
                statement.append(transaction.toString()).append("\n");
                count++;
            }
        }
        
        if (count == 0) {
            statement.append("No transactions found in the specified period.\n");
        }
        
        statement.append("========================================\n");
        statement.append("Filtered Transactions: ").append(count).append("\n");
        statement.append("========================================\n");
        
        return statement.toString();
    }


    //@ requires type != null;
    //@ requires description != null;
    //@ assignable transactionHistory, transactionHistory.*;
    //@ ensures transactionHistory.size() == \old(transactionHistory.size()) + 1;
    //@ helper
    private void addTransaction(Transaction.TransactionType type, double amount, 
                                String description, double balanceAfter) {
        transactionHistory.add(new Transaction(type, amount, description, balanceAfter));
}
}
