module
import EthLib.EVM.Proofs

open EthLib.EVM EthLib.EVM.TransactionTransfer EthLib.EVM.TransactionState.Reference
open EthLib.EVM.TransactionAccount

example (s : TransactionTransfer.State) (a b : World.Address) (x : Word) := moveEther_refines s a b x
example (s t : TransactionTransfer.State) (a b : World.Address) (x : Word) := insufficient_iff s t a b x
example (s t : TransactionTransfer.State) (a b : World.Address) (x : Word) := overflow_iff s t a b x
example (s t : TransactionTransfer.State) (a b : World.Address) (x : Word) := success_iff s t a b x
example (v w : View) (a : World.Address) (f : World.Account → World.Account) (h : ModifySpec v w a f) :=
  modify_selected v w a f h
example (v w : View) (a b : World.Address) (f : World.Account → World.Account)
    (h : ModifySpec v w a f) (hne : b ≠ a) := modify_other v w a b f h hne
example (a b : Word) := debit_exact a b
example (a b : Word) (h : a.toNat + b.toNat < Word.modulus) := credit_exact a b h
example (v w : View) (a b : World.Address) (x : Word) (h : SuccessSpec v w a b x) (hne : a ≠ b) :=
  success_distinct_balances v w a b x h hne
example (v w : View) (a b : World.Address) (x : Word) (h : SuccessSpec v w a b x) (hne : a ≠ b) :=
  success_distinct_conservation v w a b x h hne
example (v w : View) (a : World.Address) (x : Word) (h : SuccessSpec v w a a x) :=
  success_self_balance v w a x h
example (v w : View) (a b c : World.Address) (x : Word) (h : SuccessSpec v w a b x)
    (ha : c ≠ a) (hb : c ≠ b) := success_other_account v w a b c x h ha hb
example (v w : View) (a b : World.Address) (x : Word) (h : SuccessSpec v w a b x) :=
  success_retained v w a b x h
example (s t : TransactionTransfer.State) (a b : World.Address) (x : Word) (h : moveEther s a b x = .ok t) :=
  success_snapshots s t a b x h
example (s t : TransactionTransfer.State) (a b : World.Address) (x : Word)
    (h : moveEther (TransactionState.snapshot (TransactionState.snapshot s)) a b x = .ok t) :=
  nested_rollback s t a b x h
example (s : TransactionTransfer.State) (a : World.Address) (x : Word)
    (h : x.toNat ≤ (selectedAccount (observe s) a).balance.toNat) := self_credit_in_range s a x h
example (s : TransactionTransfer.State) (a : World.Address) (x : Word) := self_success_iff s a x
example (v w : View) (a b : World.Address) (x : Word) (p : Slot) (h : SuccessSpec v w a b x)
    (ha : p.1 ≠ a) (hb : p.1 ≠ b) := success_other_storage v w a b x p h ha hb
example (v w : View) (a b c : World.Address) (x : Word) (h : SuccessSpec v w a b x) :=
  success_accountReads v w a b x c h
example (s t : TransactionTransfer.State) (a b : World.Address) (x : Word) (e : TransferError)
    (h : moveEther s a b x = .error (e, t)) := error_snapshots s t a b x e h
example (s t : TransactionTransfer.State) (a b : World.Address) (x : Word) (e : TransferError)
    (h : moveEther (TransactionState.snapshot (TransactionState.snapshot s)) a b x = .error (e, t)) :=
  nested_error_rollback s t a b x e h
