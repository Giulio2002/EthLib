module
import EthLib.EVM.Proofs

open EthLib.EVM EthLib.EVM.TransactionTracker EthLib.EVM.TransactionState.Reference

/-- Write, enter two scopes, write again, then roll back the inner scope. -/
def writeThenRollback (s : State) (a b : World.Address) (k j x y : Word) :
    Except (Sum (StorageError × State) TransactionState.SnapshotError) State :=
  match setStorage s a k x with
  | .error e => .error (.inl e)
  | .ok first =>
    match setStorage (TransactionState.snapshot (TransactionState.snapshot first)) b j y with
    | .error e => .error (.inl e)
    | .ok second =>
      match TransactionState.rollback second with
      | .error e => .error (.inr e)
      | .ok result => .ok result

/-- The program restores the first write and retains both account reads. -/
theorem writeThenRollback_spec (s first second : State) (a b : World.Address)
    (k j x y : Word) (hfirst : setStorage s a k x = .ok first)
    (hsecond : setStorage (TransactionState.snapshot (TransactionState.snapshot first)) b j y = .ok second) :
    ∃ result, writeThenRollback s a b k j x y = .ok result ∧
      (observe result).writes = (observe first).writes ∧
      (observe result).stack = (observe (TransactionState.snapshot first)).stack ∧
      (∀ c, (observe result).accountReads c ↔ c = b ∨ c = a ∨ (observe s).accountReads c) ∧
      (observe result).storageReads = (observe s).storageReads ∧
      (observe result).created = (observe s).created ∧
      (observe result).parentStorage = (observe s).parentStorage ∧
      (observe result).parentAccounts = (observe s).parentAccounts ∧
      (observe result).parentCode = (observe s).parentCode := by
  obtain ⟨result, hr, hw, hs, ha, hsr, hc, hp, hpa, hpc⟩ :=
    write_nested_rollback s first second a b k j x y hfirst hsecond
  refine ⟨result, ?_, hw, hs, ha, hsr, hc, hp, hpa, hpc⟩
  simp [writeThenRollback, hfirst, hsecond, hr]

#print axioms writeThenRollback_spec
