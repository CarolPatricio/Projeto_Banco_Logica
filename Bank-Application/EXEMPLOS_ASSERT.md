# Onde Utilizar `assert` no Projeto

O `assert` em Java é uma ferramenta de verificação de programação defensiva que pode ser usado para validar condições que devem ser verdadeiras em tempo de execução. Ele é especialmente útil quando combinado com as especificações JML já existentes no projeto.

## ⚠️ Importante
- Os `assert` são **desabilitados por padrão** em Java
- Para habilitar: execute com `java -ea` ou `java -enableassertions`
- Use `assert` para condições que **nunca deveriam ser falsas** se o código estiver correto
- Use `exceptions` para condições que podem ocorrer em uso normal (validação de entrada do usuário)

## 1. Verificar Pós-Condições (Após Operações)

### Exemplo 1: Após depósito
```java
public void deposit(double amount) throws InsufficientAmountException {
    if (!isActive) {
        throw new IllegalStateException("Cannot perform operations on a closed account.");
    }
    if(amount <= 0){
        throw new InsufficientAmountException(amount);
    }
    
    double oldBalance = balance;  // Guardar valor antigo
    balance += amount;
    addTransaction(Transaction.TransactionType.DEPOSIT, amount, balance);
    
    // Assert: verificar pós-condição (deve ser sempre verdadeiro se código está correto)
    assert balance == oldBalance + amount : "Balance should increase by amount";
    assert transactionHistory.size() > 0 : "Transaction should be added to history";
}
```

### Exemplo 2: Após saque
```java
public void withdraw(double amount, String ssn) 
        throws InsufficientBalanceException, InsufficientAmountException {
    if (!isActive) {
        throw new IllegalStateException("Cannot perform operations on a closed account.");
    }
    if (amount <= 0) {
        throw new InsufficientAmountException(amount);
    }
    if (amount > balance && !(this instanceof OverdraftAccount)) {
        throw new InsufficientBalanceException(balance, amount);
    }
    
    double oldBalance = balance;
    int oldTransactionCount = transactionHistory.size();
    
    balance -= amount;
    addTransaction(Transaction.TransactionType.WITHDRAWAL, amount, balance);
    
    // Assert: verificar pós-condições
    assert balance == oldBalance - amount : "Balance should decrease by amount";
    assert transactionHistory.size() == oldTransactionCount + 1 : "One transaction should be added";
}
```

## 2. Validar Invariantes de Classe

### Exemplo 3: No final de métodos que modificam estado
```java
public void requestLoan(double amount) throws InsufficientAmountException, InsufficientCreditException {
    if (amount <= 0) throw new InsufficientAmountException(amount);
    
    if (amount > creditLimit) {
        throw new InsufficientCreditException(creditLimit, amount);
    }
    
    if (loanBalance + amount > creditLimit) {
        double availableCredit = creditLimit - loanBalance;
        throw new InsufficientCreditException(availableCredit, amount);
    }
    
    balance += amount;
    loanBalance += amount;
    addTransaction(Transaction.TransactionType.LOAN_REQUEST, amount, balance);
    
    // Assert: verificar invariantes
    assert loanBalance <= creditLimit : "Loan balance should never exceed credit limit";
    assert loanBalance >= 0 : "Loan balance should never be negative";
    assert creditLimit >= 0 : "Credit limit should never be negative";
}
```

## 3. Verificar Pré-Condições Internas

### Exemplo 4: Em métodos privados/auxiliares
```java
private void addTransaction(Transaction.TransactionType type, double amount, double balanceAfter) {
    // Assert: verificar pré-condições (condições que devem ser verdadeiras)
    assert type != null : "Transaction type cannot be null";
    assert amount >= 0 : "Transaction amount cannot be negative";
    assert transactionHistory != null : "Transaction history cannot be null";
    
    transactionHistory.add(new Transaction(type, amount, balanceAfter));
    
    // Assert: verificar pós-condição
    assert transactionHistory.size() > 0 : "Transaction should be added";
}
```

## 4. Validar Estado Após Operações Complexas

### Exemplo 5: Após transferência
```java
public void transfer(double amount, String ssn, Account destinationAccount) 
        throws InsufficientAmountException, InsufficientBalanceException {
    if (amount <= 0) throw new InsufficientAmountException(amount);
    
    if (destinationAccount == null) {
        throw new IllegalArgumentException("Destination account cannot be null.");
    }
    
    if (this == destinationAccount) {
        throw new IllegalArgumentException("Cannot transfer to the same account.");
    }
    
    double sourceOldBalance = balance;
    double destOldBalance = destinationAccount.balance;
    
    // Realizar transferência
    balance -= amount;
    addTransaction(Transaction.TransactionType.TRANSFER_OUT, amount, balance);
    
    destinationAccount.balance += amount;
    destinationAccount.addTransaction(Transaction.TransactionType.TRANSFER_IN, amount, destinationAccount.getBalance());
    
    // Assert: verificar consistência da transferência
    assert balance == sourceOldBalance - amount : "Source balance should decrease by amount";
    assert destinationAccount.balance == destOldBalance + amount : "Destination balance should increase by amount";
    assert (sourceOldBalance + destOldBalance) == (balance + destinationAccount.balance) : 
        "Total money should be conserved in transfer";
}
```

## 5. Validar Construtor

### Exemplo 6: No construtor
```java
public Account(User holder, String iban, double balance) {
    this.holder = holder;
    this.iban = iban;
    this.balance = balance;
    this.loanBalance = 0;
    this.creditLimit = 10000.0; 
    this.interestRate = 0.05; 
    this.isActive = true;
    
    // Assert: verificar que objeto foi inicializado corretamente
    assert this.holder != null : "Holder cannot be null";
    assert this.iban != null : "IBAN cannot be null";
    assert this.balance >= 0 : "Initial balance should be non-negative";
    assert this.loanBalance == 0 : "Initial loan balance should be zero";
    assert this.isActive == true : "Account should be active initially";
    assert this.transactionHistory != null : "Transaction history should be initialized";
    
    if (balance > 0) {
        addTransaction(Transaction.TransactionType.DEPOSIT, balance, balance);
    }
}
```

## 6. Validar Métodos de Cálculo

### Exemplo 7: Em métodos de cálculo
```java
public double calculateInterest(int months) {
    if (loanBalance <= 0) return 0.0;
    
    // Assert: verificar pré-condições
    assert months >= 0 : "Months should be non-negative";
    assert loanBalance > 0 : "Loan balance should be positive to calculate interest";
    assert interestRate >= 0 : "Interest rate should be non-negative";
    
    double result = loanBalance * interestRate * (months / 12.0);
    
    // Assert: verificar pós-condição
    assert result >= 0 : "Interest should be non-negative";
    
    return result;
}
```

## 7. Validar Estado em Métodos de Consulta

### Exemplo 8: Em getters que retornam cópias
```java
public List<Transaction> getTransactionHistory() {
    // Assert: verificar invariante antes de retornar
    assert transactionHistory != null : "Transaction history should never be null";
    
    return new ArrayList<>(transactionHistory);
}
```

## Resumo: Quando Usar `assert` vs `Exception`

| Situação | Usar |
|----------|------|
| Erro de programação interno (bug) | `assert` |
| Condição que nunca deveria ser falsa | `assert` |
| Validação de entrada do usuário | `Exception` |
| Condição que pode ocorrer em uso normal | `Exception` |
| Verificação de pós-condições | `assert` |
| Verificação de invariantes | `assert` |
| Validação de parâmetros públicos | `Exception` |

## Como Habilitar Asserts

```bash
# Compilar normalmente
javac -d out src/gr/aueb/cf/**/*.java

# Executar com asserts habilitados
java -ea -cp out gr.aueb.cf.Main

# Ou desabilitar para produção
java -da -cp out gr.aueb.cf.Main
```

