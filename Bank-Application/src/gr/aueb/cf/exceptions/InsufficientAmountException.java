package gr.aueb.cf.exceptions;

/**
 * @author Ntirintis John
 */
public class InsufficientAmountException extends Exception {
    private static final long serialVersionIUD = 1234L;

    //@ requires amount <= 0;
    //@ ensures getMessage() != null;
    //@ pure
    public InsufficientAmountException(double amount){
        super("Amount" + amount + "is negative");
    }
}
