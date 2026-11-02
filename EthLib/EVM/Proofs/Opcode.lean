module

public import EthLib.EVM.Opcode
import Mathlib.Tactic

/-! Kernel-checked opcode encoding properties. -/

@[expose] public section

namespace EthLib.EVM.Proofs.Opcode

open EthLib.EVM

/-- Encoding and decoding preserve each target-subset opcode. -/
theorem decode_encode (op : Opcode) : Opcode.decode (Opcode.encode op) = some op := by
  cases op <;> try rfl
  all_goals rename_i n; fin_cases n <;> rfl

set_option maxHeartbeats 2000000 in
/-- Every decoded byte is recovered by encoding its result. -/
theorem encode_decode (b : UInt8) (op : Opcode) (h : Opcode.decode b = some op) :
    Opcode.encode op = b := by
  -- Exhaust the finite byte representation with kernel reduction.
  have check (n : Fin 256) :
      ((Opcode.decode (UInt8.ofNat n.val)).map Opcode.encode) =
        if (Opcode.decode (UInt8.ofNat n.val)).isSome then some (UInt8.ofNat n.val)
        else none := by
    fin_cases n <;> decide
  have hc := check ⟨b.toNat, UInt8.toNat_lt b⟩
  simp only [UInt8.ofNat_toNat, h, Option.map, Option.isSome,
    ↓reduceIte, Option.some.injEq] at hc
  exact hc

/-- The byte representation distinguishes opcodes. -/
theorem encode_injective : Function.Injective Opcode.encode := by
  intro a b h
  have ha := decode_encode a
  have hb := decode_encode b
  rw [h] at ha
  rw [hb] at ha
  exact (Option.some.inj ha).symm

/-- Decoding returns exactly the opcode whose encoding is the input byte. -/
theorem decode_eq_some_iff (b : UInt8) (op : Opcode) :
    Opcode.decode b = some op ↔ Opcode.encode op = b := by
  constructor
  · exact encode_decode b op
  · intro h
    rw [← h]
    exact decode_encode op

/-- Independently enumerated Cancun byte and opcode pairs plus Osaka CLZ and Amsterdam SLOTNUM.

The Cancun EELS `Ops` enum supplies the dispatched pairs.
Yellow Paper Appendix H.2 supplies the designated INVALID byte.
Osaka execution-specs `vm.instructions.Ops` supplies CLZ.
Amsterdam `vm.instructions.Ops` supplies SLOTNUM.
-/
def reference : List (UInt8 × Opcode) := [
  (0x00, .stop),
  (0x01, .add),
  (0x02, .mul),
  (0x03, .sub),
  (0x04, .div),
  (0x05, .sdiv),
  (0x06, .mod),
  (0x07, .smod),
  (0x08, .addmod),
  (0x09, .mulmod),
  (0x0a, .exp),
  (0x0b, .signextend),
  (0x10, .lt),
  (0x11, .gt),
  (0x12, .slt),
  (0x13, .sgt),
  (0x14, .eq),
  (0x15, .iszero),
  (0x16, .and),
  (0x17, .or),
  (0x18, .xor),
  (0x19, .not),
  (0x1a, .byte),
  (0x1b, .shl),
  (0x1c, .shr),
  (0x1d, .sar),
  (0x1e, .clz),
  (0x20, .keccak),
  (0x30, .address),
  (0x31, .balance),
  (0x32, .origin),
  (0x33, .caller),
  (0x34, .callvalue),
  (0x35, .calldataload),
  (0x36, .calldatasize),
  (0x37, .calldatacopy),
  (0x38, .codesize),
  (0x39, .codecopy),
  (0x3a, .gasprice),
  (0x3b, .extcodesize),
  (0x3c, .extcodecopy),
  (0x3d, .returndatasize),
  (0x3e, .returndatacopy),
  (0x3f, .extcodehash),
  (0x40, .blockhash),
  (0x41, .coinbase),
  (0x42, .timestamp),
  (0x43, .number),
  (0x44, .prevrandao),
  (0x45, .gaslimit),
  (0x46, .chainid),
  (0x47, .selfbalance),
  (0x48, .basefee),
  (0x49, .blobhash),
  (0x4a, .blobbasefee),
  (0x4b, .slotnum),
  (0x50, .pop),
  (0x51, .mload),
  (0x52, .mstore),
  (0x53, .mstore8),
  (0x54, .sload),
  (0x55, .sstore),
  (0x56, .jump),
  (0x57, .jumpi),
  (0x58, .pc),
  (0x59, .msize),
  (0x5a, .gas),
  (0x5b, .jumpdest),
  (0x5c, .tload),
  (0x5d, .tstore),
  (0x5e, .mcopy),
  (0x5f, .push ⟨0, by decide⟩),
  (0x60, .push ⟨1, by decide⟩),
  (0x61, .push ⟨2, by decide⟩),
  (0x62, .push ⟨3, by decide⟩),
  (0x63, .push ⟨4, by decide⟩),
  (0x64, .push ⟨5, by decide⟩),
  (0x65, .push ⟨6, by decide⟩),
  (0x66, .push ⟨7, by decide⟩),
  (0x67, .push ⟨8, by decide⟩),
  (0x68, .push ⟨9, by decide⟩),
  (0x69, .push ⟨10, by decide⟩),
  (0x6a, .push ⟨11, by decide⟩),
  (0x6b, .push ⟨12, by decide⟩),
  (0x6c, .push ⟨13, by decide⟩),
  (0x6d, .push ⟨14, by decide⟩),
  (0x6e, .push ⟨15, by decide⟩),
  (0x6f, .push ⟨16, by decide⟩),
  (0x70, .push ⟨17, by decide⟩),
  (0x71, .push ⟨18, by decide⟩),
  (0x72, .push ⟨19, by decide⟩),
  (0x73, .push ⟨20, by decide⟩),
  (0x74, .push ⟨21, by decide⟩),
  (0x75, .push ⟨22, by decide⟩),
  (0x76, .push ⟨23, by decide⟩),
  (0x77, .push ⟨24, by decide⟩),
  (0x78, .push ⟨25, by decide⟩),
  (0x79, .push ⟨26, by decide⟩),
  (0x7a, .push ⟨27, by decide⟩),
  (0x7b, .push ⟨28, by decide⟩),
  (0x7c, .push ⟨29, by decide⟩),
  (0x7d, .push ⟨30, by decide⟩),
  (0x7e, .push ⟨31, by decide⟩),
  (0x7f, .push ⟨32, by decide⟩),
  (0x80, .dup ⟨0, by decide⟩),
  (0x81, .dup ⟨1, by decide⟩),
  (0x82, .dup ⟨2, by decide⟩),
  (0x83, .dup ⟨3, by decide⟩),
  (0x84, .dup ⟨4, by decide⟩),
  (0x85, .dup ⟨5, by decide⟩),
  (0x86, .dup ⟨6, by decide⟩),
  (0x87, .dup ⟨7, by decide⟩),
  (0x88, .dup ⟨8, by decide⟩),
  (0x89, .dup ⟨9, by decide⟩),
  (0x8a, .dup ⟨10, by decide⟩),
  (0x8b, .dup ⟨11, by decide⟩),
  (0x8c, .dup ⟨12, by decide⟩),
  (0x8d, .dup ⟨13, by decide⟩),
  (0x8e, .dup ⟨14, by decide⟩),
  (0x8f, .dup ⟨15, by decide⟩),
  (0x90, .swap ⟨0, by decide⟩),
  (0x91, .swap ⟨1, by decide⟩),
  (0x92, .swap ⟨2, by decide⟩),
  (0x93, .swap ⟨3, by decide⟩),
  (0x94, .swap ⟨4, by decide⟩),
  (0x95, .swap ⟨5, by decide⟩),
  (0x96, .swap ⟨6, by decide⟩),
  (0x97, .swap ⟨7, by decide⟩),
  (0x98, .swap ⟨8, by decide⟩),
  (0x99, .swap ⟨9, by decide⟩),
  (0x9a, .swap ⟨10, by decide⟩),
  (0x9b, .swap ⟨11, by decide⟩),
  (0x9c, .swap ⟨12, by decide⟩),
  (0x9d, .swap ⟨13, by decide⟩),
  (0x9e, .swap ⟨14, by decide⟩),
  (0x9f, .swap ⟨15, by decide⟩),
  (0xa0, .log ⟨0, by decide⟩),
  (0xa1, .log ⟨1, by decide⟩),
  (0xa2, .log ⟨2, by decide⟩),
  (0xa3, .log ⟨3, by decide⟩),
  (0xa4, .log ⟨4, by decide⟩),
  (0xf0, .create),
  (0xf1, .call),
  (0xf2, .callcode),
  (0xf3, .return),
  (0xf4, .delegatecall),
  (0xf5, .create2),
  (0xfa, .staticcall),
  (0xfd, .revert),
  (0xfe, .invalid),
  (0xff, .selfdestruct)]

/-- The historical Cancun table excludes the later CLZ and SLOTNUM assignments. -/
def cancunReference : List (UInt8 × Opcode) := reference.filter (fun pair => pair.1 != 0x1e && pair.1 != 0x4b)

set_option maxHeartbeats 4000000 in
/-- The historical classifier agrees with every entry and gap in the Cancun table. -/
theorem decodeCancun_reference (b : UInt8) : Opcode.decodeCancun b = cancunReference.lookup b := by
  have check (n : Fin 256) :
      Opcode.decodeCancun (UInt8.ofNat n.val) = cancunReference.lookup (UInt8.ofNat n.val) := by
    fin_cases n <;> decide
  simpa only [UInt8.ofNat_toNat] using check ⟨b.toNat, UInt8.toNat_lt b⟩

/-- Cancun plus Osaka CLZ excludes the later SLOTNUM assignment. -/
def cancunClzReference : List (UInt8 × Opcode) := reference.filter (fun pair => pair.1 != 0x4b)

set_option maxHeartbeats 4000000 in
/-- The Cancun-plus-CLZ classifier agrees with the historical table at every byte. -/
theorem decodeCancunClz_reference (b : UInt8) :
    Opcode.decodeCancunClz b = cancunClzReference.lookup b := by
  have check (n : Fin 256) :
      Opcode.decodeCancunClz (UInt8.ofNat n.val) = cancunClzReference.lookup (UInt8.ofNat n.val) := by
    fin_cases n <;> decide
  simpa only [UInt8.ofNat_toNat] using check ⟨b.toNat, UInt8.toNat_lt b⟩

set_option maxHeartbeats 4000000 in
/-- The decoder agrees with every entry and every gap in the source table. -/
theorem decode_reference (b : UInt8) : Opcode.decode b = reference.lookup b := by
  have check (n : Fin 256) :
      Opcode.decode (UInt8.ofNat n.val) = reference.lookup (UInt8.ofNat n.val) := by
    fin_cases n <;> decide
  simpa only [UInt8.ofNat_toNat] using check ⟨b.toNat, UInt8.toNat_lt b⟩

/-- Successful decoding is exactly membership in the pinned reference table. -/
theorem decode_success_iff (b : UInt8) :
    (∃ op, Opcode.decode b = some op) ↔ ∃ op, reference.lookup b = some op := by
  rw [decode_reference]

/-- An unassigned byte is exactly a gap in the pinned reference table. -/
theorem decode_unassigned_iff (b : UInt8) :
    Opcode.decode b = none ↔ reference.lookup b = none := by
  rw [decode_reference]

/-- The designated invalid instruction has its own constructor. -/
theorem decode_invalid : Opcode.decode 0xfe = some .invalid := by decide

/-- Only the designated byte decodes to INVALID. -/
theorem decode_invalid_iff (b : UInt8) :
    Opcode.decode b = some .invalid ↔ b = 0xfe := by
  rw [decode_eq_some_iff]
  simp [Opcode.encode, eq_comm]

end EthLib.EVM.Proofs.Opcode
