module

/-!
# Sparse byte contents

Cancun execution-specs `vm/memory.py`, `memory_write` and `memory_read_bytes`:
https://github.com/ethereum/execution-specs/blob/fd9298410ec7218838c8348f69c1eb633f1797dc/src/ethereum/forks/cancun/vm/memory.py

This module models byte contents only.
It does not model allocation or the bounds of the source bytearray.
-/

@[expose] public section

namespace EthLib.EVM.Memory

/-- A finite history of byte writes, newest first.

Every list is valid, including histories with duplicate addresses or zero bytes.
The list length is unrelated to allocated memory size.
-/
abbrev Store := List (Nat × UInt8)

/-- The store with no writes. -/
def empty : Store := []

/-- Observe the newest write at an address, or zero if none exists. -/
def readByte : Store → Nat → UInt8
  | [], _ => 0
  | (address, value) :: rest, query =>
    if address = query then value else readByte rest query

/-- Record a byte write without allocating the intervening addresses. -/
def writeByte (store : Store) (address : Nat) (value : UInt8) : Store :=
  (address, value) :: store

/-- The total byte function observed from a finite store. -/
def contents (store : Store) : Nat → UInt8 := readByte store

/-- Addresses occurring in a finite history, including shadowed and zero writes. -/
def support (store : Store) : List Nat := store.map Prod.fst

end EthLib.EVM.Memory
