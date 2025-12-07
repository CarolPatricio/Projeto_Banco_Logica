# Plano de Aplicação de JML (Java Modeling Language)

## 📋 Visão Geral

Este documento divide o trabalho de aplicação de JML (Java Modeling Language) no projeto Bank-Application entre duas pessoas. JML é uma linguagem de especificação formal que permite definir contratos, pré-condições, pós-condições e invariantes para métodos e classes Java.

---

## 👥 Divisão do Trabalho

### **Pessoa 1 - Responsabilidades:**
- Classes de Modelo Básicas
- Classes de Exceções
- Classe Transaction

### **Pessoa 2 - Responsabilidades:**
- Classe Account (principal e complexa)
- Classe Card
- Classes de Conta Especializadas (OverdraftAccount, JointAccount, OverdraftJointAccount)

---

## 📝 PESSOA 1 - Tarefas Detalhadas

### **FASE 1: Preparação e Configuração (1-2 horas)**

#### Passo 1.1: Configurar Ambiente JML
- [ ] Instalar OpenJML ou JML2
- [ ] Configurar IDE (Eclipse/IntelliJ) com suporte JML
- [ ] Criar arquivo de configuração JML
- [ ] Testar compilação JML com um exemplo simples

#### Passo 1.2: Estudar Documentação
- [ ] Revisar sintaxe JML básica
- [ ] Entender anotações: `@requires`, `@ensures`, `@invariant`, `@assignable`
- [ ] Estudar exemplos de especificações JML

---

### **FASE 2: Classes Básicas (3-4 horas)**

#### Passo 2.1: IdentifiableEntity.java
**Objetivo:** Especificar invariantes e contratos básicos

```java
// Exemplo de especificações a adicionar:
//@ public invariant getId() >= 0;
//@ public invariant getId() == 0 || getId() > 0;

//@ requires id >= 0;
//@ ensures getId() == id;
public void setId(long id) { ... }
```

**Tarefas:**
- [ ] Adicionar invariantes para ID
- [ ] Especificar pré-condições em setters
- [ ] Especificar pós-condições em getters
- [ ] Documentar modificações permitidas

---

#### Passo 2.2: User.java
**Objetivo:** Especificar contratos para operações de usuário

**Especificações necessárias:**
- [ ] Invariantes: firstName, lastName, ssn não podem ser null após construção válida
- [ ] Pré-condições em construtores
- [ ] Pós-condições em getters/setters
- [ ] Especificar comportamento do copy constructor

**Exemplo:**
```java
//@ requires firstName != null && lastName != null && ssn != null;
//@ requires !firstName.isEmpty() && !lastName.isEmpty() && !ssn.isEmpty();
//@ ensures getFirstName().equals(firstName);
//@ ensures getLastName().equals(lastName);
//@ ensures getSsn().equals(ssn);
public User(String firstName, String lastName, String ssn) { ... }

//@ requires firstName != null && !firstName.isEmpty();
//@ ensures getFirstName().equals(firstName);
//@ assignable this.firstName;
public void setFirstName(String firstName) { ... }
```

---

#### Passo 2.3: Transaction.java
**Objetivo:** Especificar contratos para transações

**Especificações necessárias:**
- [ ] Invariantes: amount >= 0, date não pode ser null
- [ ] Pré-condições em construtor
- [ ] Pós-condições em getters
- [ ] Especificar tipos de transação válidos

**Exemplo:**
```java
//@ requires type != null;
//@ requires amount >= 0;
//@ requires description != null;
//@ requires balanceAfter >= 0;
//@ ensures getType() == type;
//@ ensures getAmount() == amount;
//@ ensures getDate() != null;
//@ ensures getBalanceAfter() == balanceAfter;
public Transaction(TransactionType type, double amount, String description, double balanceAfter) { ... }
```

---

### **FASE 3: Classes de Exceções (2-3 horas)**

#### Passo 3.1: InsufficientAmountException.java
- [ ] Especificar quando a exceção deve ser lançada
- [ ] Documentar pré-condições que levam à exceção

#### Passo 3.2: InsufficientBalanceException.java
- [ ] Especificar condições de saldo insuficiente
- [ ] Documentar parâmetros da exceção

#### Passo 3.3: InsufficientCreditException.java
- [ ] Especificar condições de crédito insuficiente
- [ ] Documentar limites de crédito

#### Passo 3.4: SsnNotValidException.java
- [ ] Especificar condições de SSN inválido
- [ ] Documentar validações necessárias

**Exemplo para exceções:**
```java
//@ requires amount <= 0;
//@ signals (InsufficientAmountException e) amount <= 0;
//@ ensures \result != null;
public InsufficientAmountException(double amount) { ... }
```

---

### **FASE 4: Testes e Validação (2-3 horas)**

#### Passo 4.1: Compilar com JML
- [ ] Compilar todas as classes especificadas
- [ ] Corrigir erros de sintaxe JML
- [ ] Verificar warnings

#### Passo 4.2: Documentar Especificações
- [ ] Criar documento resumindo especificações adicionadas
- [ ] Documentar decisões de design
- [ ] Listar invariantes principais

---

## 📝 PESSOA 2 - Tarefas Detalhadas

### **FASE 1: Preparação e Configuração (1-2 horas)**

#### Passo 1.1: Configurar Ambiente JML
- [ ] Instalar OpenJML ou JML2
- [ ] Configurar IDE com suporte JML
- [ ] Sincronizar com Pessoa 1 sobre configurações
- [ ] Testar compilação JML

#### Passo 1.2: Estudar Classes Complexas
- [ ] Analisar classe Account em detalhes
- [ ] Mapear todos os métodos e suas dependências
- [ ] Identificar invariantes críticos
- [ ] Estudar padrões JML para sistemas bancários

---

### **FASE 2: Classe Account (6-8 horas) - PRIORIDADE ALTA**

#### Passo 2.1: Invariantes da Classe
**Objetivo:** Definir invariantes que sempre devem ser verdadeiros

```java
//@ public invariant creditLimit > 0;
//@ public invariant interestRate >= 0 && interestRate <= 1;
//@ public invariant loanBalance >= 0;
//@ public invariant loanBalance <= creditLimit;
//@ public invariant transactionHistory != null;
//@ public invariant holder != null;
//@ public invariant iban != null && !iban.isEmpty();
```

**Tarefas:**
- [ ] Definir invariantes de valores numéricos (balance, loanBalance, creditLimit)
- [ ] Definir invariantes de referências não-nulas
- [ ] Definir invariantes de relacionamentos (loanBalance <= creditLimit)
- [ ] Validar invariantes em todos os métodos

---

#### Passo 2.2: Construtores
**Objetivo:** Especificar pré-condições e pós-condições dos construtores

```java
//@ requires holder != null;
//@ requires iban != null && !iban.isEmpty();
//@ requires balance >= 0;
//@ ensures getHolder().equals(holder);
//@ ensures getIban().equals(iban);
//@ ensures getBalance() == balance;
//@ ensures getLoanBalance() == 0;
//@ ensures getCreditLimit() == 10000.0;
//@ ensures getInterestRate() == 0.05;
//@ ensures isActive() == true;
//@ ensures getTransactionHistory().size() >= 0;
public Account(User holder, String iban, double balance) { ... }
```

**Tarefas:**
- [ ] Especificar construtor padrão
- [ ] Especificar construtor com parâmetros
- [ ] Documentar inicialização de campos

---

#### Passo 2.3: Métodos de Depósito e Saque
**Objetivo:** Especificar contratos para operações financeiras básicas

**deposit():**
```java
//@ requires isActive() == true;
//@ requires amount > 0;
//@ ensures getBalance() == \old(getBalance()) + amount;
//@ ensures getTransactionHistory().size() == \old(getTransactionHistory().size()) + 1;
//@ assignable balance, transactionHistory;
//@ signals (IllegalStateException e) !isActive();
//@ signals (InsufficientAmountException e) amount <= 0;
public void deposit(double amount) throws InsufficientAmountException { ... }
```

**withdraw():**
```java
//@ requires isActive() == true;
//@ requires amount > 0;
//@ requires amount <= getBalance() || this instanceof OverdraftAccount;
//@ requires isSsnValid(ssn);
//@ ensures getBalance() == \old(getBalance()) - amount;
//@ assignable balance, transactionHistory;
//@ signals (IllegalStateException e) !isActive();
//@ signals (InsufficientAmountException e) amount <= 0;
//@ signals (InsufficientBalanceException e) amount > getBalance() && !(this instanceof OverdraftAccount);
//@ signals (SsnNotValidException e) !isSsnValid(ssn);
public void withdraw(double amount, String ssn) throws ... { ... }
```

**Tarefas:**
- [ ] Especificar deposit() com todas as condições
- [ ] Especificar withdraw() considerando contas normais e overdraft
- [ ] Especificar validação de SSN
- [ ] Documentar atualização do histórico

---

#### Passo 2.4: Métodos de Empréstimo
**Objetivo:** Especificar contratos para sistema de empréstimos

**requestLoan():**
```java
//@ requires isActive() == true;
//@ requires amount > 0;
//@ requires amount <= creditLimit;
//@ requires loanBalance + amount <= creditLimit;
//@ ensures getBalance() == \old(getBalance()) + amount;
//@ ensures getLoanBalance() == \old(getLoanBalance()) + amount;
//@ ensures getLoanBalance() <= creditLimit;
//@ assignable balance, loanBalance, transactionHistory;
//@ signals (InsufficientAmountException e) amount <= 0;
//@ signals (InsufficientCreditException e) amount > creditLimit || loanBalance + amount > creditLimit;
public void requestLoan(double amount) throws ... { ... }
```

**repayLoan():**
```java
//@ requires isActive() == true;
//@ requires amount > 0;
//@ requires amount <= getBalance();
//@ requires amount <= getLoanBalance();
//@ ensures getBalance() == \old(getBalance()) - amount;
//@ ensures getLoanBalance() == \old(getLoanBalance()) - amount;
//@ ensures getLoanBalance() >= 0;
//@ assignable balance, loanBalance, transactionHistory;
public void repayLoan(double amount) throws ... { ... }
```

**Tarefas:**
- [ ] Especificar requestLoan() com validações de limite
- [ ] Especificar repayLoan() com validações
- [ ] Especificar métodos auxiliares (calculateInterest, isEligibleForLoan)

---

#### Passo 2.5: Métodos de Transferência
**Objetivo:** Especificar contratos para transferências entre contas

```java
//@ requires isActive() == true;
//@ requires destinationAccount != null;
//@ requires destinationAccount != this;
//@ requires amount > 0;
//@ requires isSsnValid(ssn);
//@ requires amount <= getBalance() || this instanceof OverdraftAccount;
//@ ensures getBalance() == \old(getBalance()) - amount;
//@ ensures destinationAccount.getBalance() == \old(destinationAccount.getBalance()) + amount;
//@ assignable balance, transactionHistory, destinationAccount.balance, destinationAccount.transactionHistory;
//@ signals (IllegalArgumentException e) destinationAccount == null || destinationAccount == this;
//@ signals (SsnNotValidException e) !isSsnValid(ssn);
public void transfer(double amount, String ssn, Account destinationAccount) throws ... { ... }
```

**Tarefas:**
- [ ] Especificar transfer() com todas as validações
- [ ] Documentar efeitos em ambas as contas
- [ ] Especificar atualização de histórico em ambas as contas

---

#### Passo 2.6: Métodos de Gerenciamento de Conta
**Objetivo:** Especificar contratos para fechar conta e alterar dados

**closeAccount():**
```java
//@ requires isSsnValid(ssn);
//@ requires getBalance() == 0;
//@ requires getLoanBalance() == 0;
//@ ensures isActive() == false;
//@ assignable isActive, transactionHistory;
//@ signals (SsnNotValidException e) !isSsnValid(ssn);
//@ signals (IllegalStateException e) getBalance() != 0 || getLoanBalance() != 0 || !isActive();
public void closeAccount(String ssn) throws ... { ... }
```

**updateHolderName():**
```java
//@ requires isActive() == true;
//@ requires isSsnValid(ssn);
//@ requires newFirstName != null && !newFirstName.isEmpty();
//@ requires newLastName != null && !newLastName.isEmpty();
//@ ensures getHolder().getFirstName().equals(newFirstName);
//@ ensures getHolder().getLastName().equals(newLastName);
//@ assignable holder;
//@ signals (IllegalStateException e) !isActive();
//@ signals (SsnNotValidException e) !isSsnValid(ssn);
public void updateHolderName(String newFirstName, String newLastName, String ssn) throws ... { ... }
```

**Tarefas:**
- [ ] Especificar closeAccount() com todas as condições
- [ ] Especificar métodos de atualização de dados
- [ ] Especificar generateStatement()

---

### **FASE 3: Classe Card (4-5 horas)**

#### Passo 3.1: Invariantes da Classe Card
```java
//@ public invariant holder != null;
//@ public invariant account != null;
//@ public invariant number != null && !number.isEmpty();
//@ public invariant creditLimit >= 0;
//@ public invariant bill >= 0;
//@ public invariant bill <= creditLimit;
```

#### Passo 3.2: Métodos de Compra
**creditPurchase():**
```java
//@ requires amount >= 0;
//@ requires isSsnValid(ssn);
//@ requires amount <= creditLimit;
//@ ensures getCreditLimit() == \old(getCreditLimit()) - amount;
//@ ensures getBill() == \old(getBill()) + amount;
//@ assignable creditLimit, bill;
public void creditPurchase(double amount, String ssn, String number, String pin, String cvv) throws ... { ... }
```

**Tarefas:**
- [ ] Especificar creditPurchase()
- [ ] Especificar debitPurchase()
- [ ] Especificar payBillWithBalance()

---

### **FASE 4: Classes Especializadas (3-4 horas)**

#### Passo 4.1: OverdraftAccount.java
**Objetivo:** Especificar comportamento especial de contas overdraft

**Especificações principais:**
- [ ] Sobrescrever especificação de withdraw() para permitir saldo negativo
- [ ] Manter invariantes da classe base
- [ ] Especificar que não há verificação de saldo em withdraw()

```java
//@ also
//@ requires amount > 0;
//@ requires isSsnValid(ssn);
//@ ensures getBalance() == \old(getBalance()) - amount;
//@ ensures getBalance() pode ser negativo;
//@ assignable balance, transactionHistory;
public void withdraw(double amount, String ssn) throws ... { ... }
```

---

#### Passo 4.2: JointAccount.java
**Objetivo:** Especificar comportamento de contas conjuntas

**Especificações principais:**
- [ ] Especificar que isSsnValid() aceita SSN de qualquer titular
- [ ] Manter invariantes da classe base
- [ ] Especificar segundo titular

```java
//@ public invariant secondHolder != null;
//@ ensures \result == super.isSsnValid(ssn) || secondHolder.getSsn().equals(ssn);
protected boolean isSsnValid(String ssn) { ... }
```

---

#### Passo 4.3: OverdraftJointAccount.java
**Objetivo:** Especificar combinação de overdraft e joint account

**Tarefas:**
- [ ] Combinar especificações de OverdraftAccount e JointAccount
- [ ] Garantir que todas as invariantes são mantidas

---

### **FASE 5: Testes e Validação (2-3 horas)**

#### Passo 5.1: Compilar com JML
- [ ] Compilar todas as classes especificadas
- [ ] Corrigir erros de sintaxe JML
- [ ] Resolver conflitos de especificação

#### Passo 5.2: Validação de Contratos
- [ ] Executar verificador estático JML (se disponível)
- [ ] Validar que invariantes são mantidos
- [ ] Testar casos extremos

#### Passo 5.3: Documentação Final
- [ ] Criar documento resumindo todas as especificações
- [ ] Documentar decisões de design
- [ ] Listar todos os invariantes

---

## 🔄 Sincronização entre as Pessoas

### **Checkpoints Obrigatórios:**

1. **Após Fase 1 (Preparação):**
   - [ ] Ambas as pessoas confirmam ambiente configurado
   - [ ] Compartilhar configurações JML
   - [ ] Definir padrões de estilo para especificações

2. **Após Fase 2/3 (Classes Básicas vs Account):**
   - [ ] Revisar especificações juntas
   - [ ] Garantir consistência entre classes
   - [ ] Validar que Account usa corretamente User e Transaction

3. **Antes de Fase Final:**
   - [ ] Integrar especificações
   - [ ] Resolver conflitos
   - [ ] Validar compilação completa

---

## 📚 Recursos e Referências

### **Documentação JML:**
- JML Reference Manual
- OpenJML Documentation
- Exemplos de especificações JML

### **Padrões Importantes:**
- Sempre especificar `@requires` para pré-condições
- Sempre especificar `@ensures` para pós-condições
- Usar `\old()` para referenciar valores anteriores
- Especificar `@assignable` para campos modificados
- Usar `@signals` para exceções

### **Boas Práticas:**
- Invariantes devem ser sempre verdadeiros
- Pré-condições devem ser verificáveis
- Pós-condições devem ser testáveis
- Documentar todas as exceções possíveis

---

## ⏱️ Estimativa de Tempo Total

- **Pessoa 1:** 8-12 horas
- **Pessoa 2:** 16-22 horas (Account é mais complexa)
- **Total:** 24-34 horas

---

## ✅ Checklist Final

### **Antes de Considerar Completo:**
- [ ] Todas as classes têm especificações JML
- [ ] Todos os métodos públicos têm contratos
- [ ] Invariantes estão definidos e validados
- [ ] Código compila com JML sem erros
- [ ] Documentação está completa
- [ ] Ambas as pessoas revisaram o trabalho

---

## 📝 Notas Importantes

1. **Prioridade:** Começar pela classe Account (Pessoa 2) pois é a mais complexa
2. **Comunicação:** Manter comunicação constante sobre decisões de design
3. **Testes:** Testar especificações com casos reais do Main.java
4. **Versionamento:** Commitar especificações JML incrementalmente
5. **Revisão:** Revisar especificações juntas antes de finalizar

---

**Boa sorte com a aplicação de JML! 🚀**

