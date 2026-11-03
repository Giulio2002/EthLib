module

public import EthLib.EVM.TransactionAccount

/-!
# Amsterdam transaction tracker value transfer

The source is `forks/amsterdam/state_tracker.py`, `move_ether`, at
execution-specs revision `fd9298410ec7218838c8348f69c1eb633f1797dc`.
The pinned `ethereum-types` 0.4.1 `Unsigned` and `FixedUnsigned` arithmetic
rejects results outside `0 <= x < 2^256`.
Failures carry the tracker at the source operation's failure boundary.
They are library errors, not EVM exceptional-halt classifications.
-/

@[expose] public section
namespace EthLib.EVM.TransactionTransfer

abbrev State := TransactionState.State
abbrev Address := World.Address

/-- The source assertion or checked recipient addition failed. -/
inductive TransferError where
  | insufficientBalance
  | recipientOverflow
  deriving DecidableEq, Repr

/-- Amsterdam `move_ether`, including checked arithmetic and read effects.

A direct zero transfer executes both account modifications.
The recipient is read after the sender update, including when addresses match.
-/
def moveEther (s : State) (sender recipient : Address) (amount : Word) :
    Except (TransferError × State) State :=
  let senderRead := TransactionTracker.getAccount s sender
  if senderRead.1.balance.toNat < amount.toNat then
    .error (.insufficientBalance, senderRead.2)
  else
    let debited := TransactionAccount.setAccountBalance s sender
      (BitVec.ofNat 256 (senderRead.1.balance.toNat - amount.toNat))
    let recipientRead := TransactionTracker.getAccount debited recipient
    if recipientRead.1.balance.toNat + amount.toNat ≥ Word.modulus then
      .error (.recipientOverflow, recipientRead.2)
    else
      .ok (TransactionAccount.setAccountBalance debited recipient
        (BitVec.ofNat 256 (recipientRead.1.balance.toNat + amount.toNat)))

end EthLib.EVM.TransactionTransfer
