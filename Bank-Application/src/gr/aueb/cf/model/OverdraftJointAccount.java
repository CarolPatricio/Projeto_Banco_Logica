package gr.aueb.cf.model;

import gr.aueb.cf.exceptions.InsufficientAmountException;
import gr.aueb.cf.exceptions.InsufficientBalanceException;
import gr.aueb.cf.exceptions.SsnNotValidException;

/**
 * The {@code OverdraftJointAccount} class represents a joint bank account
 * which allows overdraft, i.e., the account's balance can go negative.
 * This class extends the {@code JointAccount} class and overrides the withdraw method
 * to remove the balance check, thereby allowing an overdraft.
 *
 * @author Ntirintis John
 */
public class OverdraftJointAccount extends JointAccount{

    /**
     * Overloaded constructor initializing an overdraft joint account with a first holder, IBAN, initial balance and second holder.
     *
     * @param holder the first user who holds the account
     * @param iban the international bank account number of the account
     * @param balance the initial balance of the account
     * @param secondHolder the second user who holds the account
     */
    //@ requires holder != null;
    //@ requires iban != null;
    //@ requires balance >= 0;
    public OverdraftJointAccount(User holder, String iban, double balance) {
        super(holder, iban, balance);
    }

    /**
     * Withdraws a given amount from the joint bank account if the holder's social security number (SSN)
     * matches the one given. Unlike the parent {@code JointAccount} class, it allows the balance to go negative (overdraft).
     *
     * @param amount the amount to be withdrawn
     * @param ssn the social security number of the account holder
     * @throws SsnNotValidException if the social security number doesn't match the holder's SSN
     * @throws InsufficientAmountException if the amount is zero or negative
     */
    //@ also
    //@ public normal_behavior
    //@   requires isActive;
    //@   requires amount > 0;
    //@   requires ssn != null;
    //@   requires transactionHistory != null;
    //@   assignable balance, transactionHistory.values;
    //@   ensures balance == \old(balance) - amount;
    //@   ensures transactionHistory.size() == \old(transactionHistory.size()) + 1;
    //@ also
    //@ public exceptional_behavior
    //@   requires !isActive;
    //@   signals (IllegalStateException);
    //@ also
    //@ public exceptional_behavior
    //@   requires isActive;
    //@   requires amount <= 0;
    //@   signals (InsufficientAmountException) amount <= 0;
    @Override
    public void withdraw(double amount, String ssn) throws InsufficientAmountException {
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
