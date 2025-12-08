package gr.aueb.cf.model;

/**
 * The {@code IdentifiableEntity} class provides a base model
 * for objects which need a unique identifier. This identifier is represented
 * as a {@code long}.
 *
 * @author Ntirintis John
 */
public class IdentifiableEntity {
    //@ spec_public
    private long id;
    
    //@ public invariant id >= 0;
    //@ public constraint id == \old(id);

    //@ ensures \result == id;
    //@ ensures \result >= 0;
    //@ pure
    public long getId() {
        return id;
    }
}
