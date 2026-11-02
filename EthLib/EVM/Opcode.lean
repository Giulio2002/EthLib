module

/-!
# Opcode bytes for the implemented target subset

The source is execution-specs revision `fd9298410ec7218838c8348f69c1eb633f1797dc`,
Cancun `vm.instructions.Ops` and `op_implementation`, with CLZ from Osaka
and SLOTNUM from Amsterdam.
The designated INVALID byte is named by the Shanghai Yellow Paper Appendix H.2.
Decoding an opcode does not implement its execution.
-/

@[expose] public section

namespace EthLib.EVM

/-- Cancun opcode bytes plus Osaka CLZ and Amsterdam SLOTNUM, including INVALID. -/
inductive Opcode where
  | stop
  | add
  | mul
  | sub
  | div
  | sdiv
  | mod
  | smod
  | addmod
  | mulmod
  | exp
  | signextend
  | lt
  | gt
  | slt
  | sgt
  | eq
  | iszero
  | and
  | or
  | xor
  | not
  | byte
  | shl
  | shr
  | sar
  | clz
  | keccak
  | address
  | balance
  | origin
  | caller
  | callvalue
  | calldataload
  | calldatasize
  | calldatacopy
  | codesize
  | codecopy
  | gasprice
  | extcodesize
  | extcodecopy
  | returndatasize
  | returndatacopy
  | extcodehash
  | blockhash
  | coinbase
  | timestamp
  | number
  | slotnum
  | prevrandao
  | gaslimit
  | chainid
  | selfbalance
  | basefee
  | blobhash
  | blobbasefee
  | pop
  | mload
  | mstore
  | mstore8
  | sload
  | sstore
  | jump
  | jumpi
  | pc
  | msize
  | gas
  | jumpdest
  | tload
  | tstore
  | mcopy
  | create
  | call
  | callcode
  | return
  | delegatecall
  | create2
  | staticcall
  | revert
  | invalid
  | selfdestruct
  /-- PUSH0 through PUSH32, indexed by immediate length. -/
  | push (length : Fin 33)
  /-- DUP1 through DUP16, indexed from zero. -/
  | dup (index : Fin 16)
  /-- SWAP1 through SWAP16, indexed from zero. -/
  | swap (index : Fin 16)
  /-- LOG0 through LOG4, indexed by topic count. -/
  | log (topics : Fin 5)
  deriving DecidableEq, Repr

namespace Opcode

/-- Decode an assigned byte, or return none for an unassigned byte. -/
def decode (byte : UInt8) : Option Opcode :=
  match byte.toNat with
  | 0x00 => some .stop
  | 0x01 => some .add
  | 0x02 => some .mul
  | 0x03 => some .sub
  | 0x04 => some .div
  | 0x05 => some .sdiv
  | 0x06 => some .mod
  | 0x07 => some .smod
  | 0x08 => some .addmod
  | 0x09 => some .mulmod
  | 0x0a => some .exp
  | 0x0b => some .signextend
  | 0x10 => some .lt
  | 0x11 => some .gt
  | 0x12 => some .slt
  | 0x13 => some .sgt
  | 0x14 => some .eq
  | 0x15 => some .iszero
  | 0x16 => some .and
  | 0x17 => some .or
  | 0x18 => some .xor
  | 0x19 => some .not
  | 0x1a => some .byte
  | 0x1b => some .shl
  | 0x1c => some .shr
  | 0x1d => some .sar
  | 0x1e => some .clz
  | 0x20 => some .keccak
  | 0x30 => some .address
  | 0x31 => some .balance
  | 0x32 => some .origin
  | 0x33 => some .caller
  | 0x34 => some .callvalue
  | 0x35 => some .calldataload
  | 0x36 => some .calldatasize
  | 0x37 => some .calldatacopy
  | 0x38 => some .codesize
  | 0x39 => some .codecopy
  | 0x3a => some .gasprice
  | 0x3b => some .extcodesize
  | 0x3c => some .extcodecopy
  | 0x3d => some .returndatasize
  | 0x3e => some .returndatacopy
  | 0x3f => some .extcodehash
  | 0x40 => some .blockhash
  | 0x41 => some .coinbase
  | 0x42 => some .timestamp
  | 0x4b => some .slotnum
  | 0x43 => some .number
  | 0x44 => some .prevrandao
  | 0x45 => some .gaslimit
  | 0x46 => some .chainid
  | 0x47 => some .selfbalance
  | 0x48 => some .basefee
  | 0x49 => some .blobhash
  | 0x4a => some .blobbasefee
  | 0x50 => some .pop
  | 0x51 => some .mload
  | 0x52 => some .mstore
  | 0x53 => some .mstore8
  | 0x54 => some .sload
  | 0x55 => some .sstore
  | 0x56 => some .jump
  | 0x57 => some .jumpi
  | 0x58 => some .pc
  | 0x59 => some .msize
  | 0x5a => some .gas
  | 0x5b => some .jumpdest
  | 0x5c => some .tload
  | 0x5d => some .tstore
  | 0x5e => some .mcopy
  | 0xf0 => some .create
  | 0xf1 => some .call
  | 0xf2 => some .callcode
  | 0xf3 => some .return
  | 0xf4 => some .delegatecall
  | 0xf5 => some .create2
  | 0xfa => some .staticcall
  | 0xfd => some .revert
  | 0xfe => some .invalid
  | 0xff => some .selfdestruct
  | 0x5f => some (.push ⟨0, by decide⟩)
  | 0x60 => some (.push ⟨1, by decide⟩)
  | 0x61 => some (.push ⟨2, by decide⟩)
  | 0x62 => some (.push ⟨3, by decide⟩)
  | 0x63 => some (.push ⟨4, by decide⟩)
  | 0x64 => some (.push ⟨5, by decide⟩)
  | 0x65 => some (.push ⟨6, by decide⟩)
  | 0x66 => some (.push ⟨7, by decide⟩)
  | 0x67 => some (.push ⟨8, by decide⟩)
  | 0x68 => some (.push ⟨9, by decide⟩)
  | 0x69 => some (.push ⟨10, by decide⟩)
  | 0x6a => some (.push ⟨11, by decide⟩)
  | 0x6b => some (.push ⟨12, by decide⟩)
  | 0x6c => some (.push ⟨13, by decide⟩)
  | 0x6d => some (.push ⟨14, by decide⟩)
  | 0x6e => some (.push ⟨15, by decide⟩)
  | 0x6f => some (.push ⟨16, by decide⟩)
  | 0x70 => some (.push ⟨17, by decide⟩)
  | 0x71 => some (.push ⟨18, by decide⟩)
  | 0x72 => some (.push ⟨19, by decide⟩)
  | 0x73 => some (.push ⟨20, by decide⟩)
  | 0x74 => some (.push ⟨21, by decide⟩)
  | 0x75 => some (.push ⟨22, by decide⟩)
  | 0x76 => some (.push ⟨23, by decide⟩)
  | 0x77 => some (.push ⟨24, by decide⟩)
  | 0x78 => some (.push ⟨25, by decide⟩)
  | 0x79 => some (.push ⟨26, by decide⟩)
  | 0x7a => some (.push ⟨27, by decide⟩)
  | 0x7b => some (.push ⟨28, by decide⟩)
  | 0x7c => some (.push ⟨29, by decide⟩)
  | 0x7d => some (.push ⟨30, by decide⟩)
  | 0x7e => some (.push ⟨31, by decide⟩)
  | 0x7f => some (.push ⟨32, by decide⟩)
  | 0x80 => some (.dup ⟨0, by decide⟩)
  | 0x81 => some (.dup ⟨1, by decide⟩)
  | 0x82 => some (.dup ⟨2, by decide⟩)
  | 0x83 => some (.dup ⟨3, by decide⟩)
  | 0x84 => some (.dup ⟨4, by decide⟩)
  | 0x85 => some (.dup ⟨5, by decide⟩)
  | 0x86 => some (.dup ⟨6, by decide⟩)
  | 0x87 => some (.dup ⟨7, by decide⟩)
  | 0x88 => some (.dup ⟨8, by decide⟩)
  | 0x89 => some (.dup ⟨9, by decide⟩)
  | 0x8a => some (.dup ⟨10, by decide⟩)
  | 0x8b => some (.dup ⟨11, by decide⟩)
  | 0x8c => some (.dup ⟨12, by decide⟩)
  | 0x8d => some (.dup ⟨13, by decide⟩)
  | 0x8e => some (.dup ⟨14, by decide⟩)
  | 0x8f => some (.dup ⟨15, by decide⟩)
  | 0x90 => some (.swap ⟨0, by decide⟩)
  | 0x91 => some (.swap ⟨1, by decide⟩)
  | 0x92 => some (.swap ⟨2, by decide⟩)
  | 0x93 => some (.swap ⟨3, by decide⟩)
  | 0x94 => some (.swap ⟨4, by decide⟩)
  | 0x95 => some (.swap ⟨5, by decide⟩)
  | 0x96 => some (.swap ⟨6, by decide⟩)
  | 0x97 => some (.swap ⟨7, by decide⟩)
  | 0x98 => some (.swap ⟨8, by decide⟩)
  | 0x99 => some (.swap ⟨9, by decide⟩)
  | 0x9a => some (.swap ⟨10, by decide⟩)
  | 0x9b => some (.swap ⟨11, by decide⟩)
  | 0x9c => some (.swap ⟨12, by decide⟩)
  | 0x9d => some (.swap ⟨13, by decide⟩)
  | 0x9e => some (.swap ⟨14, by decide⟩)
  | 0x9f => some (.swap ⟨15, by decide⟩)
  | 0xa0 => some (.log ⟨0, by decide⟩)
  | 0xa1 => some (.log ⟨1, by decide⟩)
  | 0xa2 => some (.log ⟨2, by decide⟩)
  | 0xa3 => some (.log ⟨3, by decide⟩)
  | 0xa4 => some (.log ⟨4, by decide⟩)
  | _ => none

/-- The historical Cancun classifier does not assign CLZ or SLOTNUM. -/
def decodeCancun (byte : UInt8) : Option Opcode :=
  if byte = 0x1e ∨ byte = 0x4b then none else decode byte

/-- Cancun plus Osaka CLZ, without Amsterdam SLOTNUM. -/
def decodeCancunClz (byte : UInt8) : Option Opcode :=
  if byte = 0x4b then none else decode byte

/-- Encode each opcode as its unique byte. -/
def encode : Opcode → UInt8
  | .stop => 0x00
  | .add => 0x01
  | .mul => 0x02
  | .sub => 0x03
  | .div => 0x04
  | .sdiv => 0x05
  | .mod => 0x06
  | .smod => 0x07
  | .addmod => 0x08
  | .mulmod => 0x09
  | .exp => 0x0a
  | .signextend => 0x0b
  | .lt => 0x10
  | .gt => 0x11
  | .slt => 0x12
  | .sgt => 0x13
  | .eq => 0x14
  | .iszero => 0x15
  | .and => 0x16
  | .or => 0x17
  | .xor => 0x18
  | .not => 0x19
  | .byte => 0x1a
  | .shl => 0x1b
  | .shr => 0x1c
  | .sar => 0x1d
  | .clz => 0x1e
  | .keccak => 0x20
  | .address => 0x30
  | .balance => 0x31
  | .origin => 0x32
  | .caller => 0x33
  | .callvalue => 0x34
  | .calldataload => 0x35
  | .calldatasize => 0x36
  | .calldatacopy => 0x37
  | .codesize => 0x38
  | .codecopy => 0x39
  | .gasprice => 0x3a
  | .extcodesize => 0x3b
  | .extcodecopy => 0x3c
  | .returndatasize => 0x3d
  | .returndatacopy => 0x3e
  | .extcodehash => 0x3f
  | .blockhash => 0x40
  | .coinbase => 0x41
  | .timestamp => 0x42
  | .slotnum => 0x4b
  | .number => 0x43
  | .prevrandao => 0x44
  | .gaslimit => 0x45
  | .chainid => 0x46
  | .selfbalance => 0x47
  | .basefee => 0x48
  | .blobhash => 0x49
  | .blobbasefee => 0x4a
  | .pop => 0x50
  | .mload => 0x51
  | .mstore => 0x52
  | .mstore8 => 0x53
  | .sload => 0x54
  | .sstore => 0x55
  | .jump => 0x56
  | .jumpi => 0x57
  | .pc => 0x58
  | .msize => 0x59
  | .gas => 0x5a
  | .jumpdest => 0x5b
  | .tload => 0x5c
  | .tstore => 0x5d
  | .mcopy => 0x5e
  | .create => 0xf0
  | .call => 0xf1
  | .callcode => 0xf2
  | .return => 0xf3
  | .delegatecall => 0xf4
  | .create2 => 0xf5
  | .staticcall => 0xfa
  | .revert => 0xfd
  | .invalid => 0xfe
  | .selfdestruct => 0xff
  | .push n => UInt8.ofNat (0x5f + n.val)
  | .dup n => UInt8.ofNat (0x80 + n.val)
  | .swap n => UInt8.ofNat (0x90 + n.val)
  | .log n => UInt8.ofNat (0xa0 + n.val)

end Opcode
end EthLib.EVM
