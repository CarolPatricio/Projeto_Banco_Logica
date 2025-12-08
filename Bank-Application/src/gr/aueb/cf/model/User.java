package gr.aueb.cf.model;

/**
 * The {@code User} class represents a user or a holder of a bank account.
 * A user is identifiable by a social security number (SSN) and has a first name and a last name.
 * The User class extends IdentifiableEntity to include a unique ID.
 *
 * @author Ntirintis John
 */
public class User extends IdentifiableEntity {
    //@ spec_public
    private String firstName;
    //@ spec_public
    private String lastName;
    //@ spec_public
    private String ssn;
    
    //@ public invariant firstName != null;
    //@ public invariant lastName != null;
    //@ public invariant ssn != null;
    /**
     * Overloaded constructor initializing a user with first name, last name, and social security number.
     *
     * @param firstName the first name of the user
     * @param lastName the last name of the user
     * @param ssn the social security number of the user
     */
    //@ requires firstName != null && lastName != null && ssn != null;
    //@ requires !firstName.isEmpty() && !lastName.isEmpty() && !ssn.isEmpty();
    //@ ensures this.firstName == firstName;
    //@ ensures this.lastName == lastName;
    //@ ensures this.ssn == ssn;
    public User(String firstName, String lastName, String ssn) {
        this.firstName = firstName;
        this.lastName = lastName;
        this.ssn = ssn;
    }

    /**
     * Copy constructor creating a new user that is a copy of the user provided.
     *
     * @param user the user to be copied
     */
    //@ requires user != null;
    //@ requires user.firstName != null && user.lastName != null && user.ssn != null;
    //@ ensures this.firstName == user.firstName;
    //@ ensures this.lastName == user.lastName;
    //@ ensures this.ssn == user.ssn;
    public User(User user){
        firstName = user.firstName;
        lastName = user.lastName;
        ssn = user.ssn;
    }

    // Getters and Setters
    //@ ensures \result != null;
    //@ ensures \result == firstName;
    /*@ pure @*/
    public String getFirstName() {
        return firstName;
    }

    /*@ 
      @ public normal_behavior
      @   requires firstName != null && !firstName.isEmpty();
      @   assignable this.firstName;
      @   ensures this.firstName == firstName;
      @*/
    public void setFirstName(String firstName) {
        this.firstName = firstName;
    }

    //@ ensures \result != null;
    //@ ensures \result == lastName;
    /*@ pure @*/
    public String getLastName() {
        return lastName;
    }

    /*@ 
      @ public normal_behavior
      @   requires lastName != null && !lastName.isEmpty();
      @   assignable this.lastName;
      @   ensures this.lastName == lastName;
      @*/
    public void setLastName(String lastName) {
        this.lastName = lastName;
    }

    //@ ensures \result != null;
    //@ ensures \result == ssn;
    /*@ pure @*/
    public String getSsn() {
        return ssn;
    }

    //@ requires ssn != null && !ssn.isEmpty();
    //@ ensures this.ssn == ssn;
    //@ assignable this.ssn;
    public void setSsn(String ssn) {
        this.ssn = ssn;
    }

    /**
     * Returns a string representation of the user.
     * The returned string includes the user's first name, last name, and social security number.
     *
     * @return a string representation of the user
     */
     //@ skipesc
    @Override
    public String toString() {
        return "User{" +
                "firstName='" + firstName + '\'' +
                ", lastName='" + lastName + '\'' +
                ", ssn='" + ssn + '\'' +
                '}';
    }
}
