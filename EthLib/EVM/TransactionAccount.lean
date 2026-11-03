module

public import EthLib.EVM.TransactionTracker

/-!
# Amsterdam account and code tracker operations

The source is `forks/amsterdam/state_tracker.py` at execution-specs revision
`fd9298410ec7218838c8348f69c1eb633f1797dc`.
The supplied parent is the effective transaction-start world.
-/

@[expose] public section
namespace EthLib.EVM.TransactionAccount

open World

abbrev State := TransactionState.State

/-- Amsterdam `get_code`, with explicit absence for an incomplete code store. -/
def getCode (s : State) (hash : Word) : Option ByteArray :=
  if hash == emptyCodeHash then some ByteArray.empty else
    match s.writes.codeWrites.lookup hash with
    | some code => some code
    | none => World.getCode s.parent hash

/-- Amsterdam `destroy_account` clears storage before recording the deletion. -/
def destroyAccount (s : State) (a : Address) : State :=
  TransactionTracker.setAccount (TransactionTracker.destroyStorage s a) a none

/-- Amsterdam `modify_state`, including both account reads and empty cleanup. -/
def modifyState (s : State) (a : Address) (f : Account → Account) : State :=
  let read := TransactionTracker.getAccount s a
  let updated := TransactionTracker.setAccount read.2 a (some (f read.1))
  let check := TransactionTracker.getAccountOptional updated a
  if check.1 == some emptyAccount then destroyAccount check.2 a else check.2

/-- Amsterdam `set_account_balance`. -/
def setAccountBalance (s : State) (a : Address) (balance : Word) : State :=
  modifyState s a (fun account => { account with balance })

/-- Amsterdam `increment_nonce`; the nonce is an unbounded natural. -/
def incrementNonce (s : State) (a : Address) : State :=
  modifyState s a (fun account => { account with nonce := account.nonce + 1 })

/-- Amsterdam `set_code` records code by hash before modifying the account. -/
def setCode (s : State) (a : Address) (code : ByteArray) : State :=
  let hash := World.codeHash code
  let updated := if hash == emptyCodeHash then s else
    { s with writes := { s.writes with codeWrites := (hash, code) :: s.writes.codeWrites } }
  modifyState updated a (fun account => { account with codeHash := hash })

end EthLib.EVM.TransactionAccount
