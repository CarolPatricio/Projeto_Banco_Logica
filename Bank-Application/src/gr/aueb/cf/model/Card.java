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
    private User holder;
    private Account account;
    private String number;
    private String pin;
    private String cvv;
    private String expiryDate;
    private double creditLimit;
    private double bill;

    /**
     * Default constructor initializing an empty card.
     */
    public Card() {
    }

    /**
     * Overloaded constructor initializing a card with all attributes.
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
    public User getHolder() {
        return holder;
    }

    public void setHolder(User holder) {
        this.holder = holder;
    }

    public Account getAccount() {
        return account;
    }

    public void setAccount(Account account) {
        this.account = account;
    }

    public String getNumber() {
        return number;
    }

    public void setNumber(String number) {
        this.number = number;
    }

    public String getPin() {
        return pin;
    }

    public void setPin(String pin) {
        this.pin = pin;
    }

    public String getCvv() {
        return cvv;
    }

    public void setCvv(String cvv) {
        this.cvv = cvv;
    }

    public String getExpiryDate() {
        return expiryDate;
    }

    public void setExpiryDate(String expiryDate) {
        this.expiryDate = expiryDate;
    }

    public double getCreditLimit() {
        return creditLimit;
    }

    public void setCreditLimit(double creditLimit) {
        this.creditLimit = creditLimit;
    }

    // Returns a string representation of the card
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

    // Public API

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
    public void creditPurchase(double amount, String ssn, String number, String pin, String cvv)
            throws SsnNotValidException, InsufficientAmountException, InsufficientCreditException {
        try {
            if (amount < 0)
                throw new InsufficientAmountException(amount);
            if (!account.isSsnValid(ssn))
                throw new SsnNotValidException(ssn);
            if (amount > creditLimit)
                throw new InsufficientCreditException(getCreditLimit(), amount);

            creditLimit -= amount;
            bill += amount;

        } catch (InsufficientCreditException | SsnNotValidException | InsufficientAmountException e) {
            System.err.println("Error: Credit Limit Insufficient");
            throw e;
        }
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
    public void debitPurchase(double amount, String ssn)
            throws InsufficientAmountException, InsufficientBalanceException, SsnNotValidException {
        try {
            if (amount < 0)
                throw new InsufficientAmountException(amount);
            if (!account.isSsnValid(ssn))
                throw new SsnNotValidException(ssn);
            if (amount > account.getBalance())
                throw new InsufficientBalanceException(account.getBalance(), amount);

            account.withdraw(amount, ssn);

        } catch (InsufficientBalanceException | SsnNotValidException | InsufficientAmountException e) {
            System.err.println("Error: Debit Limit Insufficient");
            throw e;
        }
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
    public void payBillWithBalance(double amount, String ssn, String number)
            throws InsufficientAmountException, InsufficientBalanceException, SsnNotValidException {
        try {
            if (amount < 0)
                throw new InsufficientAmountException(amount);
            if (!account.isSsnValid(ssn))
                throw new SsnNotValidException(ssn);
            if (amount > account.getBalance())
                throw new InsufficientBalanceException(account.getBalance(), amount);

            if (amount > bill) {
                account.withdraw(bill, ssn);
                double remainingValue = amount - bill;
                bill = 0;
                System.out.println(
                        "Amount exceeds the bill, the remaining value of " + remainingValue + " was not deducted");
            } else {
                account.withdraw(amount, ssn);
                bill -= amount;
            }

        } catch (InsufficientBalanceException | SsnNotValidException | InsufficientAmountException e) {
            System.err.println("Error: Debit Limit Insufficient");
            throw e;
        }
    }
}