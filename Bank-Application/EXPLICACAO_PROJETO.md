# Explicação Completa do Projeto Bank-Application

## 📚 Índice
1. [O que é uma Conta Conjunta com Overdraft](#conta-conjunta-overdraft)
2. [Operações do Sistema](#operações)
3. [Principais Arquivos do Projeto](#arquivos)
4. [Hierarquia de Classes](#hierarquia)

---

## 🏦 O que é uma Conta Conjunta com Overdraft? {#conta-conjunta-overdraft}

### Conta Conjunta (Joint Account)
Uma **conta conjunta** é uma conta bancária compartilhada por **dois titulares**. Ambos os titulares podem:
- Realizar depósitos
- Realizar saques
- Acessar o saldo
- Usar o dinheiro da conta

**Características:**
- Dois usuários são donos da mesma conta
- Qualquer um dos dois pode fazer operações usando seu próprio SSN (Social Security Number)
- O saldo é compartilhado entre ambos

### Overdraft (Cheque Especial)
**Overdraft** é a capacidade de uma conta ter **saldo negativo**. É como um "cheque especial" ou "limite de crédito".

**Características:**
- Permite sacar mais dinheiro do que existe na conta
- O saldo pode ficar negativo (ex: -100.0)
- Não há verificação de saldo suficiente antes do saque
- Útil para emergências ou quando você precisa de dinheiro temporariamente

### Conta Conjunta com Overdraft (OverdraftJointAccount)
É a **combinação** dos dois conceitos:
- ✅ Dois titulares podem usar a conta
- ✅ Permite saldo negativo
- ✅ Qualquer um dos dois pode sacar mesmo que o saldo fique negativo

**Exemplo prático:**
- João e Maria têm uma conta conjunta com overdraft
- Saldo atual: R$ 200,00
- João pode sacar R$ 500,00 (saldo fica: -R$ 300,00)
- Maria também pode sacar usando seu próprio SSN

---

## 💳 Operações do Sistema {#operações}

O sistema bancário implementa as seguintes operações:

### 1. **Depósito (deposit)**
Adiciona dinheiro à conta.

**Regras:**
- ✅ O valor deve ser **maior que zero**
- ❌ Valores zero ou negativos geram `InsufficientAmountException`

**Exemplo:**
```java
conta.deposit(100.0);  // Adiciona 100.0 ao saldo
```

**Implementação:**
```104:118:src/gr/aueb/cf/model/Account.java
    public void withdraw(double amount, String ssn)
            throws InsufficientBalanceException, SsnNotValidException, InsufficientAmountException {
        try {
            if(amount <= 0) throw new InsufficientAmountException(amount);
            if(amount > balance) throw new InsufficientBalanceException(getBalance(), amount);
            if(!isSsnValid(ssn)) throw new SsnNotValidException(ssn);

            balance -= amount;

        } catch (InsufficientAmountException | InsufficientBalanceException | SsnNotValidException e){
            // Would be better to have more catch statements and have exception specific err messages
            System.err.println("Error: Withdrawal");
            throw e;
        }
    }
```

### 2. **Saque (withdraw)**
Remove dinheiro da conta. O comportamento varia conforme o tipo de conta:

#### **Conta Normal (Account)**
- ❌ **NÃO permite** saldo negativo
- ✅ Verifica se há saldo suficiente
- ✅ Valida o SSN do titular

**Regras:**
- Valor deve ser > 0
- Saldo deve ser suficiente
- SSN deve corresponder ao titular

#### **Conta com Overdraft (OverdraftAccount)**
- ✅ **Permite** saldo negativo
- ❌ Não verifica saldo suficiente
- ✅ Valida o SSN do titular

**Regras:**
- Valor deve ser > 0
- SSN deve corresponder ao titular
- Pode ficar negativo

#### **Conta Conjunta (JointAccount)**
- ❌ **NÃO permite** saldo negativo
- ✅ Verifica se há saldo suficiente
- ✅ Aceita SSN de **qualquer um dos dois titulares**

**Regras:**
- Valor deve ser > 0
- Saldo deve ser suficiente
- SSN deve corresponder ao **primeiro OU segundo titular**

#### **Conta Conjunta com Overdraft (OverdraftJointAccount)**
- ✅ **Permite** saldo negativo
- ❌ Não verifica saldo suficiente
- ✅ Aceita SSN de **qualquer um dos dois titulares**

**Regras:**
- Valor deve ser > 0
- SSN deve corresponder ao **primeiro OU segundo titular**
- Pode ficar negativo

**Exemplo:**
```java
// Conta normal - precisa ter saldo suficiente
conta.withdraw(50.0, "2424");  // SSN do titular

// Conta conjunta - qualquer um dos dois pode sacar
contaConjunta.withdraw(50.0, "2424");  // SSN do primeiro titular
contaConjunta.withdraw(30.0, "1234");  // SSN do segundo titular
```

### 3. **Validação de SSN**
Verifica se o número de segurança social (SSN) corresponde ao titular.

**Para contas normais:**
- Verifica apenas o primeiro titular

**Para contas conjuntas:**
```73:76:src/gr/aueb/cf/model/JointAccount.java
    @Override
    protected boolean isSsnValid(String ssn) {
        return super.isSsnValid(ssn) || secondHolder.getSsn().equals(ssn);
    }
```
- Verifica o primeiro **OU** o segundo titular

---

## 📁 Principais Arquivos do Projeto {#arquivos}

### **Estrutura de Pastas:**
```
src/gr/aueb/cf/
├── Main.java                    # Ponto de entrada do programa
├── model/                       # Classes de modelo (entidades)
│   ├── IdentifiableEntity.java  # Classe base com ID
│   ├── User.java                # Representa um usuário/titular
│   ├── Account.java             # Conta bancária básica
│   ├── JointAccount.java        # Conta conjunta
│   ├── OverdraftAccount.java    # Conta com overdraft
│   └── OverdraftJointAccount.java # Conta conjunta com overdraft
├── exceptions/                  # Exceções customizadas
│   ├── InsufficientAmountException.java
│   ├── InsufficientBalanceException.java
│   └── SsnNotValidException.java
└── dao/                         # Data Access Object (padrão DAO)
    ├── IGenericDAO.java
    ├── IAccountDAO.java
    ├── AbstractDAO.java
    └── AccountDAOImpl.java
```

### **1. Main.java** - Ponto de Entrada
Arquivo principal que demonstra o funcionamento do sistema.

**O que faz:**
- Cria usuários (John e Michael)
- Cria diferentes tipos de contas
- Realiza operações de depósito e saque
- Exibe informações das contas

```18:36:src/gr/aueb/cf/Main.java
    public static void main(String[] args) {
        User john = new User("John", "N.", "2424");
        User michael =  new User("Michael", "W. ", "1234");

        Account acc = new Account(john, "GR2424", 100);
        Account overJohn = new OverdraftAccount(john, "GR2424", 50);
        Account overJointAccount = new OverdraftJointAccount(john, "GR2424", 200, michael);
        try {
            // .toString has been override so there is no need to call it
            System.out.println("Account: \n" + acc);
            System.out.println("Overdraft: \n" + overJohn);

            overJointAccount.deposit(100);
            overJointAccount.withdraw(50, "2424");
            System.out.println("Overdraft joint account: \n" + overJointAccount);
        } catch (InsufficientAmountException | InsufficientBalanceException | SsnNotValidException e){
            System.out.println(e.getMessage());
        }
    }
```

### **2. Model - Classes de Entidade**

#### **IdentifiableEntity.java**
Classe base que fornece um ID único para todas as entidades.

```10:20:src/gr/aueb/cf/model/IdentifiableEntity.java
public class IdentifiableEntity {
    private long id;

    public long getId() {
        return id;
    }

    public void setId(long id) {
        this.id = id;
    }
}
```

#### **User.java**
Representa um usuário/titular da conta.

**Atributos:**
- `firstName`: Primeiro nome
- `lastName`: Sobrenome
- `ssn`: Número de segurança social (usado para autenticação)

#### **Account.java**
Classe base para todas as contas bancárias.

**Atributos:**
- `holder`: Titular da conta (User)
- `iban`: Número da conta bancária internacional
- `balance`: Saldo atual

**Métodos principais:**
- `deposit(double amount)`: Deposita dinheiro
- `withdraw(double amount, String ssn)`: Saca dinheiro (com validação de saldo)

#### **JointAccount.java**
Estende `Account` para permitir dois titulares.

**Diferença principal:**
- Adiciona `secondHolder`: Segundo titular
- Sobrescreve `isSsnValid()` para aceitar SSN de qualquer um dos dois titulares

```73:76:src/gr/aueb/cf/model/JointAccount.java
    @Override
    protected boolean isSsnValid(String ssn) {
        return super.isSsnValid(ssn) || secondHolder.getSsn().equals(ssn);
    }
```

#### **OverdraftAccount.java**
Estende `Account` para permitir saldo negativo.

**Diferença principal:**
- Sobrescreve `withdraw()` removendo a verificação de saldo suficiente

```42:56:src/gr/aueb/cf/model/OverdraftAccount.java
    @Override
    public void withdraw(double amount, String ssn)
            throws SsnNotValidException, InsufficientAmountException {
        try {
            if(amount <= 0) throw new InsufficientAmountException(amount);
            if(!isSsnValid(ssn)) throw new SsnNotValidException(ssn);

            setBalance(getBalance() - amount);

        } catch (InsufficientAmountException | SsnNotValidException e){
            // Would be better to have more catch statements and have exception specific err messages
            System.err.println("Error: Withdrawal");
            throw e;
        }
    }
```

#### **OverdraftJointAccount.java**
Combina `JointAccount` + `OverdraftAccount`.

**Características:**
- Dois titulares (herdado de `JointAccount`)
- Permite saldo negativo (herdado de `OverdraftAccount`)
- Aceita SSN de qualquer um dos dois titulares

### **3. Exceptions - Exceções Customizadas**

#### **InsufficientAmountException**
Lançada quando o valor é zero ou negativo.

```6:12:src/gr/aueb/cf/exceptions/InsufficientAmountException.java
public class InsufficientAmountException extends Exception {
    private static final long serialVersionIUD = 1234L;

    public InsufficientAmountException(double amount){
        super("Amount" + amount + "is negative");
    }
}
```

#### **InsufficientBalanceException**
Lançada quando não há saldo suficiente (apenas em contas normais).

```6:17:src/gr/aueb/cf/exceptions/InsufficientBalanceException.java
public class InsufficientBalanceException extends Exception {
    // For the sake of simplicity for this example
    // we will use a simple num
    // But this should have been very long and unique
    private static final long serialVersionUID = 1234L;

    public InsufficientBalanceException() {}

    public InsufficientBalanceException(double balance, double amount) {
        super("Insufficient Balance " + balance + " for amount " + amount);
    }
}
```

#### **SsnNotValidException**
Lançada quando o SSN não corresponde ao titular.

```6:12:src/gr/aueb/cf/exceptions/SsnNotValidException.java
public class SsnNotValidException extends Exception {
    private static final long serialVersionUID = 1234L;

    public SsnNotValidException(String ssn) {
        super("Ssn" + ssn + " is not valid");
    }
}
```

### **4. DAO - Data Access Object (Opcional)**
O projeto também inclui uma estrutura DAO para persistência de dados, mas não é usada no `Main.java`.

---

## 🌳 Hierarquia de Classes {#hierarquia}

```
IdentifiableEntity (classe base)
    │
    ├── User
    │
    └── Account
            │
            ├── JointAccount
            │       │
            │       └── OverdraftJointAccount
            │
            └── OverdraftAccount
```

### **Princípios de Orientação a Objetos Utilizados:**

1. **Herança (Inheritance)**
   - `Account` herda de `IdentifiableEntity`
   - `JointAccount` e `OverdraftAccount` herdam de `Account`
   - `OverdraftJointAccount` herda de `JointAccount`

2. **Polimorfismo (Polymorphism)**
   - Método `withdraw()` é sobrescrito em diferentes classes
   - Método `isSsnValid()` é sobrescrito em `JointAccount`

3. **Encapsulamento (Encapsulation)**
   - Atributos privados com getters/setters
   - Métodos protegidos para validação interna

---

## 🔄 Fluxo de Operação no Projeto

1. **Criação de Usuários**
   ```java
   User john = new User("John", "N.", "2424");
   User michael = new User("Michael", "W. ", "1234");
   ```

2. **Criação de Contas**
   ```java
   Account acc = new Account(john, "GR2424", 100);
   Account overJohn = new OverdraftAccount(john, "GR2424", 50);
   Account overJointAccount = new OverdraftJointAccount(john, "GR2424", 200, michael);
   ```

3. **Operações**
   ```java
   overJointAccount.deposit(100);        // Saldo: 200 → 300
   overJointAccount.withdraw(50, "2424"); // Saldo: 300 → 250
   ```

4. **Exibição**
   - Usa `toString()` para mostrar informações das contas

---

## 📝 Resumo

- **Conta Conjunta com Overdraft**: Dois titulares podem usar a conta e ela permite saldo negativo
- **Operações**: Depósito (sempre válido se > 0) e Saque (com validações diferentes por tipo de conta)
- **Arquivos principais**: `Main.java` (execução), classes em `model/` (lógica de negócio), exceções em `exceptions/`
- **Padrões**: Herança, Polimorfismo, Encapsulamento, Exceções customizadas

