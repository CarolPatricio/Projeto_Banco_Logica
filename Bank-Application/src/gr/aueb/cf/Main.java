package gr.aueb.cf;

import gr.aueb.cf.exceptions.InsufficientAmountException;
import gr.aueb.cf.exceptions.InsufficientBalanceException;
import gr.aueb.cf.exceptions.SsnNotValidException;
import gr.aueb.cf.exceptions.InsufficientCreditException;
import gr.aueb.cf.model.Account;
import gr.aueb.cf.model.OverdraftAccount;
//import gr.aueb.cf.model.OverdraftJointAccount;
import gr.aueb.cf.model.User;
import gr.aueb.cf.model.Card;

/**
 * The {@code Main} class demonstrates the functionality of Account,
 * OverdraftAccount,
 * and OverdraftJointAccount by simulating deposit and withdrawal operations.
 *
 * @author Ntirintis John
 */
public class Main {
    public static void main(String[] args) {
        User john = new User("John", "N.", "2424");
        User michael = new User("Michael", "W. ", "1234");

        Account acc = new Account(john, "GR2424", 100);
        Account overJohn = new OverdraftAccount(john, "GR2424", 100);
        //Account overJointAccount = new OverdraftJointAccount(john, "GR2424", 200, michael);

        Card card = new Card(john, acc, "1234567890123456", "123", "123", "12/24", 500);

        try {
            // .toString has been override so there is no need to call it
            System.out.println("Account: \n" + acc);
            System.out.println("Overdraft: \n" + overJohn);

            acc.deposit(1000);
            //overJointAccount.deposit(100);
            //overJointAccount.withdraw(50, "2424");
            //System.out.println("Overdraft joint account: \n" + overJointAccount);

            card.creditPurchase(100, "2424", "1234567890123456", "123", "123");
            // card.debitPurchase(100, "2424");
            System.out.println("Card: \n" + card);

            card.payBillWithBalance(150, "2424", "1234567890123456");
            System.out.println("Card: \n" + card);

            // Enhanced loan functionality demonstration
            System.out.println("\n=== Loan System ===");
            System.out.println("Account credit limit: " + acc.getCreditLimit());
            System.out.println("Interest rate: " + (acc.getInterestRate() * 100) + "%");
            System.out.println("Eligible for loan: " + acc.isEligibleForLoan());
            System.out.println("Available credit: " + acc.getAvailableCredit());
            
            // Request a loan
            System.out.println("\nRequesting loan of 500.0...");
            acc.requestLoan(500);
            System.out.println("After Loan Request: " + acc);
            System.out.println("Loan Balance: " + acc.getLoanBalance());
            System.out.println("Available credit: " + acc.getAvailableCredit());
            
            // Calculate interest for 12 months
            double interest12Months = acc.calculateInterest(12);
            double totalAmount = acc.calculateTotalLoanAmount(12);
            System.out.println("\nInterest for 12 months: " + interest12Months);
            System.out.println("Total amount to repay (12 months): " + totalAmount);
            
            // Repay part of the loan
            System.out.println("\nRepaying loan of 200.0...");
            acc.repayLoan(200.0);
            System.out.println("Loan Balance: " + acc.getLoanBalance());
            System.out.println("Available credit: " + acc.getAvailableCredit());
            
            // Try to request a loan that exceeds credit limit
            System.out.println("\nTrying to request loan of 15000.0 (exceeds credit limit)...");
            try {
                acc.requestLoan(15000.0);
            } catch (InsufficientCreditException e) {
                System.out.println("Error: " + e.getMessage());
            }

            // Account transfer example
            System.out.println("\n=== Account Transfer ===");
            Account acc2 = new Account(michael, "GR5678", 500);
            System.out.println("Before transfer:");
            System.out.println("Source account (John): " + acc);
            System.out.println("Destination account (Michael): " + acc2);
            
            acc.transfer(200, "2424", acc2);
            System.out.println("\nAfter transfer of 200.0:");
            System.out.println("Source account (John): " + acc);
            System.out.println("Destination account (Michael): " + acc2);

            // Account management features
            System.out.println("\n=== Account Management ===");
            
            // Update holder information
            System.out.println("\nUpdating holder's name...");
            System.out.println("Before: " + acc.getHolder());
            acc.updateHolderName("John", "Smith");
            System.out.println("After: " + acc.getHolder());
            
            // Generate account statement
            System.out.println("\n=== Account Statement ===");
            System.out.println(acc.generateStatement());
            
            // Try to close account with balance (should fail)
            System.out.println("\n=== Attempting to Close Account ===");
            System.out.println("Current balance: " + acc.getBalance());
            System.out.println("Current loan balance: " + acc.getLoanBalance());
            try {
                acc.closeAccount();
            } catch (IllegalStateException e) {
                System.out.println("Cannot close account: " + e.getMessage());
            }
            
            // Repay remaining loan and withdraw balance
            System.out.println("\nRepaying remaining loan...");
            acc.repayLoan(acc.getLoanBalance());
            System.out.println("Withdrawing remaining balance...");
            acc.withdraw(acc.getBalance(), "2424");
            
            // Now close the account
            System.out.println("\nClosing account...");
            acc.closeAccount();
            System.out.println("Account status: " + (acc.isActive() ? "ACTIVE" : "CLOSED"));
            
            // Try to perform operations on closed account (should fail)
            System.out.println("\nTrying to deposit on closed account...");
            try {
                acc.deposit(100);
            } catch (IllegalStateException e) {
                System.out.println("Error: " + e.getMessage());
            }

        } catch (InsufficientAmountException | InsufficientBalanceException | SsnNotValidException
                | InsufficientCreditException e) {
            System.out.println(e.getMessage());
        }
    }
}
