module

public import EthLib.EVM.PushImmediate

/-!
# Cancun jump destinations

The source is execution-specs revision `fd9298410ec7218838c8348f69c1eb633f1797dc`,
Cancun `vm.runtime.get_valid_jump_destinations`.
The scan visits instruction boundaries throughout the code.
-/

@[expose] public section

namespace EthLib.EVM.JumpDest

/-- Advance past the opcode and any PUSH immediate. -/
def nextPC (code : ByteArray) (pc : Nat) : Nat :=
  match Opcode.decode (PushImmediate.byteAt code pc) with
  | some (.push length) => PushImmediate.nextPC pc length
  | _ => pc + 1

/-- Visit instruction boundaries until the end of the code. -/
def scanFrom (code : ByteArray) (pc : Nat) : List Nat :=
  if pc < code.size then
    let rest := scanFrom code (nextPC code pc)
    if PushImmediate.byteAt code pc == 0x5b then pc :: rest else rest
  else []
termination_by code.size - pc
decreasing_by
  unfold nextPC PushImmediate.nextPC
  split <;> simp_wf <;> omega

/-- The valid jump destinations in increasing program-counter order. -/
def destinations (code : ByteArray) : List Nat := scanFrom code 0

/-- Test whether a program counter is a valid jump destination. -/
def contains (code : ByteArray) (pc : Nat) : Bool := (destinations code).contains pc

end EthLib.EVM.JumpDest
