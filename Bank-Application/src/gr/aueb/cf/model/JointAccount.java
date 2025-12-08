package gr.aueb.cf.model;

/**
 * The {@code JointAccount} class represents a bank account which is jointly held by two users.
 * This class extends the {@code Account} class to include a second holder.
 * The account balance can be accessed and manipulated by either holder.
 *
 * @author Ntirintis John
 */
public class JointAccount extends Account {
    //@ spec_public nullable
    private User secondHolder;

    /**
     * Overloaded constructor initializing a joint account with a first holder, IBAN, initial balance and second holder.
     *
     * @param holder the first user who holds the account
     * @param iban the international bank account number of the account
     * @param balance the initial balance of the account
     * @param secondHolder the second user who holds the account
     */
    //@ requires holder != null;
    //@ requires iban != null;
    //@ requires balance >= 0;
    //@ ensures this.holder == holder;
    //@ ensures this.iban == iban;
    //@ ensures this.balance == balance;
    public JointAccount(User holder, String iban, double balance) {
        super(holder, iban, balance);
    }

    /**
     * @return the second holder of the account
     */

    //@ nullable
    public /*@ pure @*/ User getSecondHolder() {
        return secondHolder;
    }

    /**
     * @param secondHolder the user to set as the second holder of the account
     */
    //@ public normal_behavior
    //@   requires secondHolder != null;
    //@   assignable this.secondHolder;
    //@   ensures this.secondHolder == secondHolder;
    public void setSecondHolder(User secondHolder) {
        this.secondHolder = secondHolder;
    }


    /**
     * Returns a string representation of the joint account.
     */
    //@ skipesc
    @Override
    public String toString() {
        return "JointAccount{" + " First Holder =" + getHolder() +
                ", secondHolder=" + secondHolder + ", iban" + getIban() + ", balance " +
                getBalance() + '}';
    }


    /**
     * Checks if a given social security number (SSN) is the same as either the first or the second account holder's.
     *
     * @param ssn the social security number to be checked
     * @return true if the given SSN matches either the first or the second holder's, false otherwise
     */
    //@ skipesc
    @Override
    public boolean isSsnValid(String ssn) {
        return super.isSsnValid(ssn) || secondHolder.getSsn().equals(ssn);
    }
}
