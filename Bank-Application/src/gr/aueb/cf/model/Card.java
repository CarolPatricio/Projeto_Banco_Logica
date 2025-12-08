package gr.aueb.cf.model;

import gr.aueb.cf.exceptions.InsufficientAmountException;
import gr.aueb.cf.exceptions.InsufficientBalanceException;
import gr.aueb.cf.exceptions.SsnNotValidException;
import gr.aueb.cf.exceptions.InsufficientCreditException;

/**
 * The {@code Card} class represents a bank card associated with an account and
 * a user, identified by a unique number.
 * It provides methods for purchases with credit and debit.
 * 
 * @author Maria Amanda Morais
 */
public class Card {
    //@ spec_public
    //@ nullable
    private User holder;
    //@ spec_public
    //@ nullable
    private Account account;
    //@ spec_public
    //@ nullable
    private String number;
    //@ spec_public
    //@ nullable
    private String pin;
    //@ spec_public
    //@ nullable
    private String cvv;
    //@ spec_public
    //@ nullable
    private String expiryDate;
    //@ spec_public
    private double creditLimit;
    //@ spec_public
    private double bill;

    //@ public invariant holder != null;
    //@ public invariant account != null;
    //@ public invariant number != null;
    //@ public invariant pin != null;
    //@ public invariant cvv != null;
    //@ public invariant expiryDate != null;
    //@ public invariant creditLimit >= 0;
    //@ public initially bill == 0;
    //@ public invariant bill >= 0;
    //@ public constraint number.equals(\old(number));

    /**
     * Constructor initializing a card with all attributes.
     * 
     * @param holder      the user who holds the card.
     * @param account     the account associated with the card.
     * @param number      the card number.
     * @param pin         the card pin.
     * @param cvv         the card cvv.
     * @param expiryDate  the card expiry date.
     * @param creditLimit the card credit limit.
     * @param bill        the card bill has the initial value of 0.
     */
    //@ requires holder != null;
    //@ requires account != null;
    //@ requires number != null && !number.isEmpty();
    //@ requires pin != null;
    //@ requires cvv != null;
    //@ requires expiryDate != null;
    //@ requires creditLimit >= 0;
    //@ ensures this.holder == holder;
    //@ ensures this.account == account;
    //@ ensures this.number == number;
    //@ ensures this.pin == pin;
    //@ ensures this.cvv == cvv;
    //@ ensures this.expiryDate == expiryDate;
    //@ ensures this.creditLimit == creditLimit;
    //@ ensures this.bill == 0;
    public Card(User holder, Account account, String number, String pin, String cvv, String expiryDate,
            double creditLimit) {
        this.holder = holder;
        this.account = account;
        this.number = number;
        this.pin = pin;
        this.cvv = cvv;
        this.expiryDate = expiryDate;
        this.creditLimit = creditLimit;
        this.bill = 0;
    }

    // Getters / Setters
    //@ ensures \result != null;
    //@ ensures \result == holder;
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
    //@ ensures \result == account;
    //@ pure
    public Account getAccount() {
        return account;
    }

    //@ requires account != null;
    //@ assignable this.account;
    //@ ensures this.account == account;
    public void setAccount(Account account) {
        this.account = account;
    }

    //@ ensures \result != null;
    //@ ensures \result == number;
    //@ pure
    public String getNumber() {
        return number;
    }

    //@ ensures \result != null;
    //@ ensures \result == pin;
    //@ pure
    public String getPin() {
        return pin;
    }

    //@ requires pin != null;
    //@ assignable this.pin;
    //@ ensures this.pin == pin;
    public void setPin(String pin) {
        this.pin = pin;
    }

    //@ ensures \result != null;
    //@ ensures \result == cvv;
    //@ pure
    public String getCvv() {
        return cvv;
    }

    //@ requires cvv != null;
    //@ assignable this.cvv;
    //@ ensures this.cvv == cvv;
    public void setCvv(String cvv) {
        this.cvv = cvv;
    }

    //@ ensures \result != null;
    //@ ensures \result == expiryDate;
    //@ pure
    public String getExpiryDate() {
        return expiryDate;
    }

    //@ requires expiryDate != null;
    //@ assignable this.expiryDate;
    //@ ensures this.expiryDate == expiryDate;
    public void setExpiryDate(String expiryDate) {
        this.expiryDate = expiryDate;
    }

    //@ ensures \result == creditLimit;
    //@ pure
    public double getCreditLimit() {
        return creditLimit;
    }

    //@ requires creditLimit >= 0;
    //@ assignable this.creditLimit;
    //@ ensures this.creditLimit == creditLimit;
    public void setCreditLimit(double creditLimit) {
        this.creditLimit = creditLimit;
    }

    // Returns a string representation of the card
    //@ skipesc
    @Override
    public String toString() {
        return "Card{" +
                "holder=" + holder.toString() +
                ", account=" + account.toString() +
                ", number='" + number + '\'' +
                ", pin='" + pin + '\'' +
                ", cvv='" + cvv + '\'' +
                ", expiryDate='" + expiryDate + '\'' +
                ", creditLimit=" + creditLimit +
                ", bill=" + bill +
                '}';
    }


    /**
     * This method allows the user to make a credit purchase.
     * 
     * @param amount the amount of the purchase
     * @param ssn    the social security number of the user
     * @param number the number of the card
     * @param pin    the pin of the card
     * @param cvv    the cvv of the card
     * @throws SsnNotValidException        if the ssn is not valid
     * @throws InsufficientAmountException if the amount is zero or negative
     * @throws InsufficientCreditException if the credit limit is not valid
     */
    //@ public behavior
    //@   requires amount >= 0;
    //@   requires amount <= creditLimit;
    //@   requires holder != null;
    //@   requires account != null;
    //@   requires number != null;
    //@   requires pin != null;
    //@   requires cvv != null;
    //@   requires account.isSsnValid(ssn);
    //@   assignable creditLimit, bill;
    //@   ensures creditLimit == \old(creditLimit) - amount;
    //@   ensures bill == \old(bill) + amount;
    //@ also
    //@ public exceptional_behavior
    //@   requires amount < 0;
    //@   requires holder != null;
    //@   requires account != null;
    //@   requires number != null;
    //@   requires pin != null;
    //@   requires cvv != null;
    //@   assignable \nothing;
    //@   signals (InsufficientAmountException e) amount < 0;
    //@ also
    //@ public exceptional_behavior
    //@   requires amount >= 0;
    //@   requires amount <= creditLimit;
    //@   requires holder != null;
    //@   requires account != null;
    //@   requires number != null;
    //@   requires pin != null;
    //@   requires cvv != null;
    //@   requires !account.isSsnValid(ssn);
    //@   assignable \nothing;
    //@   signals (SsnNotValidException e) true;
    //@ also
    //@ public exceptional_behavior
    //@   requires amount >= 0;
    //@   requires amount > creditLimit;
    //@   requires holder != null;
    //@   requires account != null;
    //@   requires number != null;
    //@   requires pin != null;
    //@   requires cvv != null;
    //@   assignable \nothing;
    //@   signals (InsufficientCreditException e) amount > creditLimit;
    public void creditPurchase(double amount, String ssn, String number, String pin, String cvv)
            throws SsnNotValidException, InsufficientAmountException, InsufficientCreditException {
        if (amount < 0)
            throw new InsufficientAmountException(amount);
        if (!account.isSsnValid(ssn))
            throw new SsnNotValidException(ssn);
        if (amount > creditLimit)
            throw new InsufficientCreditException(getCreditLimit(), amount);

        creditLimit -= amount;
        bill += amount;
    }

    /**
     * This method allows the user to make a debit purchase.
     * 
     * @param amount the amount of the purchase.
     * @param ssn    the social security number of the user.
     * @throws InsufficientAmountException  if the amount is zero or negative.
     * @throws InsufficientBalanceException if the balance is not valid.
     * @throws SsnNotValidException         if the ssn is not valid.
     */
    //@ public behavior
    //@   requires amount > 0;
    //@   requires amount <= account.getBalance();
    //@   requires holder != null;
    //@   requires account != null;
    //@   requires account.transactionHistory != null;
    //@   requires account.isSsnValid(ssn);
    //@   assignable account.balance, account.transactionHistory.values;
    //@   ensures account.getBalance() == \old(account.getBalance()) - amount;
    //@ also
    //@ public exceptional_behavior
    //@   requires amount < 0;
    //@   requires holder != null;
    //@   requires account != null;
    //@   assignable \nothing;
    //@   signals (InsufficientAmountException e) amount < 0;
    //@ also
    //@ public exceptional_behavior
    //@   requires amount >= 0;
    //@   requires holder != null;
    //@   requires account != null;
    //@   requires !account.isSsnValid(ssn);
    //@   assignable \nothing;
    //@   signals (SsnNotValidException e) true;
    //@ also
    //@ public exceptional_behavior
    //@   requires amount > 0;
    //@   requires amount > account.getBalance();
    //@   requires holder != null;
    //@   requires account != null;
    //@   assignable \nothing;
    //@   signals (InsufficientBalanceException e) amount > account.getBalance();
    public void debitPurchase(double amount, String ssn)
            throws InsufficientAmountException, InsufficientBalanceException, SsnNotValidException {
        if (amount < 0)
            throw new InsufficientAmountException(amount);
        if (!account.isSsnValid(ssn))
            throw new SsnNotValidException(ssn);
        if (amount > account.getBalance())
            throw new InsufficientBalanceException(account.getBalance(), amount);

        account.withdraw(amount, ssn);
    }

    /**
     * This method allows the user to pay a bill with the balance.
     * 
     * @param amount the amount being paid.
     * @param ssn    the social security number of the user.
     * @param number the number of the card.
     * @throws InsufficientAmountException  if the amount is zero or negative.
     * @throws InsufficientBalanceException if the balance is not valid.
     * @throws SsnNotValidException         if the ssn is not valid.
     */
    //@ public behavior
    //@   requires amount > 0;
    //@   requires amount <= account.getBalance();
    //@   requires amount > bill;
    //@   requires holder != null;
    //@   requires account != null;
    //@   requires account.transactionHistory != null;
    //@   requires account.isSsnValid(ssn);
    //@   assignable account.balance, account.transactionHistory.values, bill;
    //@   ensures bill == 0;
    //@   ensures account.getBalance() == \old(account.getBalance()) - \old(bill);
    //@ also
    //@ public behavior
    //@   requires amount > 0;
    //@   requires amount <= account.getBalance();
    //@   requires amount <= bill;
    //@   requires holder != null;
    //@   requires account != null;
    //@   requires account.transactionHistory != null;
    //@   requires account.isSsnValid(ssn);
    //@   assignable account.balance, account.transactionHistory.values, bill;
    //@   ensures bill == \old(bill) - amount;
    //@   ensures account.getBalance() == \old(account.getBalance()) - amount;
    //@ also
    //@ public exceptional_behavior
    //@   requires amount < 0;
    //@   requires holder != null;
    //@   requires account != null;
    //@   assignable \nothing;
    //@   signals (InsufficientAmountException e) amount < 0;
    //@ also
    //@ public exceptional_behavior
    //@   requires amount >= 0;
    //@   requires holder != null;
    //@   requires account != null;
    //@   requires !account.isSsnValid(ssn);
    //@   assignable \nothing;
    //@   signals (SsnNotValidException e) true;
    //@ also
    //@ public exceptional_behavior
    //@   requires amount > 0;
    //@   requires amount > account.getBalance();
    //@   requires holder != null;
    //@   requires account != null;
    //@   assignable \nothing;
    //@   signals (InsufficientBalanceException e) amount > account.getBalance();
    public void payBillWithBalance(double amount, String ssn, String number)
            throws InsufficientAmountException, InsufficientBalanceException, SsnNotValidException {
        if (amount < 0)
            throw new InsufficientAmountException(amount);
        if (!account.isSsnValid(ssn))
            throw new SsnNotValidException(ssn);
        if (amount > account.getBalance())
            throw new InsufficientBalanceException(account.getBalance(), amount);

        if (amount > bill) {
            account.withdraw(bill, ssn);
            bill = 0;
        } else {
            account.withdraw(amount, ssn);
            bill -= amount;
        }
    }
}