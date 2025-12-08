package gr.aueb.cf.exceptions;

/**
 * @author Maria Amanda Morais
 */
public class InsufficientCreditException extends Exception {
    private static final long serialVersionUID = 1234L;

    public InsufficientCreditException() {
    }

    //@ requires amount > credit;
    //@ ensures getMessage() != null;
    //@ pure 
    public InsufficientCreditException(double credit, double amount) {
        super("Insufficient Credit " + credit + " for amount " + amount);
    }
}
