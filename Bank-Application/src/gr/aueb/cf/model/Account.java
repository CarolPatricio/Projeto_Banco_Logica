package gr.aueb.cf.model;

import gr.aueb.cf.exceptions.InsufficientAmountException;
import gr.aueb.cf.exceptions.InsufficientBalanceException;
import gr.aueb.cf.exceptions.SsnNotValidException;
import gr.aueb.cf.exceptions.InsufficientCreditException;

/**
 * The {@code Account} class represents a bank account belonging to a user,
 * identified by a unique International Bank Account Number (IBAN).
 * It provides methods for depositing and withdrawing money from the account.
 *
 * @author Ntirintis John
 */
public class Account extends IdentifiableEntity {
    private User holder = new User();
    private String iban;
    private double balance;
    private double loanBalance;
    private double creditLimit; // Maximum loan amount allowed
    private double interestRate; // Annual interest rate (e.g., 0.05 for 5%)

    /**
     * Default constructor initializing an empty account with a new User holder.
     */
    public Account() {
        this.loanBalance = 0;
        this.creditLimit = 10000.0; // Default credit limit
        this.interestRate = 0.05; // Default 5% annual interest rate
    }

    /**
     * Overloaded constructor initializing an account with a holder, IBAN and initial balance.
     *
     * @param holder the user who holds the account
     * @param iban the international bank account number of the account
     * @param balance the initial balance of the account
     */
    public Account(User holder, String iban, double balance) {
        this.holder = holder;
        this.iban = iban;
        this.balance = balance;
        this.loanBalance = 0;
        this.creditLimit = 10000.0; // Default credit limit
        this.interestRate = 0.05; // Default 5% annual interest rate
    }

    // Getters / Setters
    public User getHolder() {
        return holder;
    }

    public void setHolder(User holder) {
        this.holder = holder;
    }

    public String getIban() {
        return iban;
    }

    public void setIban(String iban) {
        this.iban = iban;
    }

    public double getBalance() {
        return balance;
    }

    public void setBalance(double balance) {
        this.balance = balance;
    }

    public double getLoanBalance() {
        return loanBalance;
    }

    public void setLoanBalance(double loanBalance) {
        this.loanBalance = loanBalance;
    }

    public double getCreditLimit() {
        return creditLimit;
    }

    public void setCreditLimit(double creditLimit) {
        this.creditLimit = creditLimit;
    }

    public double getInterestRate() {
        return interestRate;
    }

    public void setInterestRate(double interestRate) {
        this.interestRate = interestRate;
    }

    // Returns a string representation of the account
    @Override
    public String toString() {
        return "Account{" +
                "holder=" + holder.toString() +
                ", iban='" + iban + '\'' +
                ", balance=" + balance +
                ", loanBalance=" + loanBalance +
                ", creditLimit=" + creditLimit +
                ", interestRate=" + (interestRate * 100) + "%" +
                '}';
    }

    // Public API


    /**
     * Deposits a given amount to the bank account
     *
     * @param amount amount to be deposited
     * @throws InsufficientAmountException if amount is zero or negative
     */
    public void deposit(double amount) throws InsufficientAmountException {
        try {
            if(amount <= 0){
                throw new InsufficientAmountException(amount);
            }

            balance += amount;
        } catch (InsufficientAmountException e) {
            System.err.println("Error: Negative or Zero Amount");
            throw e;
        }
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
     */
    public void withdraw(double amount, String ssn)
            throws InsufficientBalanceException, SsnNotValidException, InsufficientAmountException {
        try {
            if(amount <= 0) throw new InsufficientAmountException(amount);
            if(amount > balance) throw new InsufficientBalanceException(getBalance(), amount);
            if(!isSsnValid(ssn)) throw new SsnNotValidException(ssn);

            balance -= amount;

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
            
            // Creditar na conta destino usando o método deposit
            destinationAccount.deposit(amount);
            
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

}
