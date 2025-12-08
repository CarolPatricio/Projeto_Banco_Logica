package gr.aueb.cf.exceptions;

/**
 * @author Ntirintis John
 */
public class InsufficientBalanceException extends Exception {
    private static final long serialVersionUID = 1234L;

    public InsufficientBalanceException() {}

    //@ requires amount > balance;
    //@ ensures getMessage() != null;
    //@ pure 
    public InsufficientBalanceException(double balance, double amount) {
        super("Insufficient Balance " + balance + " for amount " + amount);
    }
}
