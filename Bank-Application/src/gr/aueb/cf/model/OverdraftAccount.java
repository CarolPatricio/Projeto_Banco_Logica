package gr.aueb.cf.model;

import gr.aueb.cf.exceptions.InsufficientAmountException;
import gr.aueb.cf.exceptions.SsnNotValidException;

/**
 * The {@code OverdraftAccount} class represents a bank account
 * which allows overdraft, i.e., the account's balance can go negative.
 * This class extends the {@code Account} class and overrides the withdraw method
 * to remove the balance check, thereby allowing an overdraft.
 *
 * @author Ntirintis John
 */
public class OverdraftAccount extends Account {

    /**
     * Overloaded constructor initializing an overdraft account with a holder, IBAN, and initial balance.
     *
     * @param holder the user who holds the account
     * @param iban the international bank account number of the account
     * @param balance the initial balance of the account
     */
    //@ requires holder != null;
    //@ requires iban != null;
    //@ requires balance >= 0;
    public OverdraftAccount(User holder, String iban, double balance) {
        super(holder, iban, balance);
    }

    /**
     * Withdraws a given amount from the bank account if the holder's social security number (SSN)
     * matches the one given. Unlike the parent {@code Account} class, it allows the balance to go negative (overdraft).
     *
     * @param amount the amount to be withdrawn
     * @param ssn the social security number of the account holder
     * @throws SsnNotValidException if the social security number doesn't match the holder's SSN
     * @throws InsufficientAmountException if the amount is zero or negative
     */
    /*@
      @ also
      @ public normal_behavior
      @   requires isActive;
      @   requires amount > 0;
      @   requires ssn != null;
      @   requires transactionHistory != null;
      @   assignable balance, transactionHistory.values;
      @   ensures balance == \old(balance) - amount;
      @   ensures transactionHistory.size() == \old(transactionHistory.size()) + 1;
      @ also
      @ public exceptional_behavior
      @   requires !isActive;
      @   assignable \nothing;
      @   signals (IllegalStateException);
      @ also
      @ public exceptional_behavior
      @   requires isActive;
      @   requires amount <= 0;
      @   assignable \nothing;
      @   signals (InsufficientAmountException) amount <= 0;
      @*/
    @Override
    public void withdraw(double amount, String ssn) 
            throws InsufficientAmountException {
        if (!isActive) {
            throw new IllegalStateException("Cannot perform operations on a closed account.");
        }
        if (amount <= 0) {
            throw new InsufficientAmountException(amount);
        }
        setBalance(getBalance() - amount);
        addTransaction(Transaction.TransactionType.WITHDRAWAL, amount, getBalance());
    }
}
