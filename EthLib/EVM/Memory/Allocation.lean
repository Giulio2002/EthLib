module

public import EthLib.EVM.Memory.Ranges

/-!
# Logical memory allocation

Cancun execution-specs vm/gas.py, calculate_gas_extend_memory:
https://github.com/ethereum/execution-specs/blob/fd9298410ec7218838c8348f69c1eb633f1797dc/src/ethereum/forks/cancun/vm/gas.py

Cancun vm/instructions/memory.py, msize and mcopy:
https://github.com/ethereum/execution-specs/blob/fd9298410ec7218838c8348f69c1eb633f1797dc/src/ethereum/forks/cancun/vm/instructions/memory.py

This module models neither gas nor exceptions nor opcode execution.
A gas layer must authorize expansion before calling these helpers.
Addresses and sizes are natural numbers and do not wrap.
-/

@[expose] public section

namespace EthLib.EVM.Memory.Allocation

open EthLib.EVM.Memory

/-- Words needed to cover a range, with empty ranges requiring no words. -/
def requiredWords (offset length : Nat) : Nat :=
  if length = 0 then 0 else (offset + length + 31) / 32

/-- Sparse contents and the independently tracked number of allocated words. -/
structure State where
  store : Store
  words : Nat
  deriving DecidableEq

/-- Observations beyond the allocated byte size must be zero. -/
def Valid (s : State) : Prop := ∀ a, s.words * 32 ≤ a → readByte s.store a = 0

/-- Initially no bytes are allocated or written. -/
def empty : State := ⟨Memory.empty, 0⟩

/-- The logical allocated size in bytes. -/
def byteSize (s : State) : Nat := s.words * 32

/-- Expand without changing the sparse contents. -/
def expand (s : State) (offset length : Nat) : State :=
  ⟨s.store, max s.words (requiredWords offset length)⟩

/-- Read a range and return the expanded state. -/
def read (s : State) (offset length : Nat) : List UInt8 × State :=
  (readRange s.store offset length, expand s offset length)

/-- Write a range and expand to cover its payload. -/
def write (s : State) (offset : Nat) (data : List UInt8) : State :=
  ⟨writeRange s.store offset data, (expand s offset data.length).words⟩

/-- Copy a source snapshot and expand to cover both ranges. -/
def copy (s : State) (destination source length : Nat) : State :=
  ⟨copyRange s.store destination source length,
    (expand (expand s source length) destination length).words⟩

end EthLib.EVM.Memory.Allocation
