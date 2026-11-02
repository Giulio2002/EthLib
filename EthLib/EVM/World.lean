module

public import EthLib.EVM.Environment

/-!
# Pure account and storage state

The source is execution-specs revision
`fd9298410ec7218838c8348f69c1eb633f1797dc`, `ethereum/state.py`,
`ethereum/state_mpt.py`, and `forks/amsterdam/state_tracker.py`.
Addresses and 32-byte values are decoded as big-endian integers.
The lists may contain repeated keys; lookup uses the first entry.
This representation describes arbitrary pure state, not chain validity.
-/

@[expose] public section
namespace EthLib.EVM.World

abbrev Address := Environment.Address

/-- `ethereum.state.EMPTY_CODE_HASH`, decoded as a big-endian word. -/
def emptyCodeHash : Word :=
  0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470

/-- The fields of `ethereum.state.Account`.

The nonce uses the source's unbounded `Uint` domain.
The code hash is not the code itself.
-/
structure Account where
  nonce : Nat
  balance : Word
  codeHash : Word
  deriving DecidableEq, Repr

/-- `ethereum.state.EMPTY_ACCOUNT`. -/
def emptyAccount : Account := ⟨0, 0, emptyCodeHash⟩

/-- Independent finite association lists for accounts, storage and code.

All lists are accepted, including duplicates and zero storage entries.
The first occurrence gives the value, and absent storage reads as zero.
No relation between code bytes and their supplied hash is assumed.
-/
structure State where
  accounts : List (Address × Account) := []
  storage : List ((Address × Word) × Word) := []
  codes : List (Word × ByteArray) := []

/-- An optional account lookup preserves absence. -/
def getAccountOptional (s : State) (a : Address) : Option Account :=
  s.accounts.lookup a

/-- The defaulting lookup follows `state_tracker.get_account`. -/
def getAccount (s : State) (a : Address) : Account :=
  (getAccountOptional s a).getD emptyAccount

/-- Unset storage reads as zero, even when the account is absent. -/
def getStorage (s : State) (a : Address) (k : Word) : Word :=
  (s.storage.lookup (a, k)).getD 0

/-- Read supplied code bytes, with the source's empty-hash special case.

`none` means the supplied code store has no entry for a nonempty hash.
The caller is responsible for code-hash consistency.
-/
def getCode (s : State) (hash : Word) : Option ByteArray :=
  if hash == emptyCodeHash then some ByteArray.empty else s.codes.lookup hash

/-- `state_tracker.account_exists`. -/
def accountExists (s : State) (a : Address) : Bool :=
  (getAccountOptional s a).isSome

/-- `state_tracker.account_exists_and_is_empty`. -/
def accountExistsAndIsEmpty (s : State) (a : Address) : Bool :=
  getAccountOptional s a == some emptyAccount

/-- Replace or remove only the account entry, retaining its storage. -/
def setAccount (s : State) (a : Address) (v : Option Account) : State :=
  let rest := s.accounts.filter (fun p => p.1 != a)
  { s with accounts := match v with | none => rest | some x => (a, x) :: rest }

/-- A storage write requires an existing account. -/
inductive StorageError where
  | missingAccount
  deriving DecidableEq, Repr

/-- Write a slot, deleting its entries when the new value is zero. -/
def setStorage (s : State) (a : Address) (k v : Word) : Except StorageError State :=
  if accountExists s a then
    let rest := s.storage.filter (fun p => p.1 != (a, k))
    .ok { s with storage := if v == 0 then rest else ((a, k), v) :: rest }
  else .error .missingAccount

/-- Remove every storage entry for an address, retaining the account. -/
def destroyStorage (s : State) (a : Address) : State :=
  { s with storage := s.storage.filter (fun p => p.1.1 != a) }

/-- Remove an account and its storage, as `state_tracker.destroy_account`. -/
def destroyAccount (s : State) (a : Address) : State :=
  setAccount (destroyStorage s a) a none

/-- Apply an account update and destroy the result if it is empty.

This follows `state_tracker.modify_state` and is distinct from `setAccount`.
-/
def modifyState (s : State) (a : Address) (f : Account → Account) : State :=
  let updated := setAccount s a (some (f (getAccount s a)))
  if accountExistsAndIsEmpty updated a then destroyAccount updated a else updated

end EthLib.EVM.World
