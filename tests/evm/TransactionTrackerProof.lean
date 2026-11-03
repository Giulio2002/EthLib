module
import EthLib.EVM.Proofs

open EthLib.EVM EthLib.EVM.TransactionTracker EthLib.EVM.TransactionState.Reference

example (s : State) (a : World.Address) := getAccountOptional_spec s a
example (s : State) (a : World.Address) := getAccount_spec s a
example (s : State) (a : World.Address) (k : Word) := getStorage_spec s a k
example (s : State) (a : World.Address) (k : Word) := getTransientStorage_spec s a k
example (s : State) (a : World.Address) (v : Option World.Account) := setAccount_spec s a v
example (s t : State) (a : World.Address) (k v : Word) (h : setStorage s a k v = .ok t) :=
  setStorage_spec s t a k v h
example (s : State) (a : World.Address) (k v : Word) := setStorage_error_iff s a k v
example (s : State) (a : World.Address) (k v : Word) := setStorage_success_iff s a k v
example (s : State) (a : World.Address) (k v : Word) := setStorage_accountRead s a k v
example (s : State) (a : World.Address) (p : Slot) := destroyStorage_storage s a p
example (s : State) (a : World.Address) := destroyStorage_effects s a
example (s : State) (a : World.Address) (p : Slot) := destroyStorage_reads s a p
example (s : State) (a b : World.Address) := markAccountCreated_spec s a b
example (s : State) (a : World.Address) := markAccountCreated_preserves s a
example (s : State) (a : World.Address) (k v : Word) := setTransientStorage_spec s a k v
example (s first second : State) (a b : World.Address) (k j x y : Word)
    (h1 : setStorage s a k x = .ok first)
    (h2 : setStorage (TransactionState.snapshot (TransactionState.snapshot first)) b j y = .ok second) :=
  write_nested_rollback s first second a b k j x y h1 h2
example (s : State) (a : World.Address) := getAccount_value s a
example (s t : State) (a : World.Address) (k v : Word) := setStorage_error_state_iff s t a k v
example (s : State) (a : World.Address) := getAccountOptional_none_iff s a
example (s t : State) (a : World.Address) (k v : Word) := setStorage_reference_error_iff s t a k v
