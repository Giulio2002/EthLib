module

public import EthLib.EVM.Proofs.Frame.Balance
public import EthLib.EVM.Proofs.TransactionAccount

/-! Source-order contracts for Amsterdam `environment.py`, `extcodesize`. -/

@[expose] public section
namespace EthLib.EVM.Frame

/-- Code selection agrees with the independent transaction code-map reference. -/
theorem extCodeBytes_reference (s : State) (a : World.Address) :
    TransactionAccount.CodeValue (TransactionState.Reference.observe s.tracker)
      (BalanceAccount s a).codeHash (ExtCodeBytes s a) := by
  have bytes := extCodeBytes_eq s a
  have account : (TransactionTracker.getAccount s.tracker a).1 = BalanceAccount s a := rfl
  have readCode (hash : Word) : TransactionAccount.getCode (TransactionTracker.getAccount s.tracker a).2 hash =
      TransactionAccount.getCode s.tracker hash := rfl
  rw [account, readCode] at bytes
  rw [← bytes]
  exact TransactionAccount.getCode_spec s.tracker (BalanceAccount s a).codeHash

/-- Underflow occurs before warming or charging. -/
theorem extCodeSize_underflow (s : State) (empty : s.stack.val = []) :
    extCodeSize s = .exception s .stackUnderflow := by
  have pop := (Proofs.Stack.pop_underflow_iff _).mpr empty
  simp [extCodeSize, pop, failStack]

/-- A gas failure keeps the operand pop and address warming. -/
theorem extCodeSize_gas (s : State) (rest : Stack) (x : Word)
    (items : s.stack.val = x :: rest.val) (gas : s.gas < ExtCodeSizeCost s (BalanceAddress x)) :
    extCodeSize s = .exception { s with stack := rest, warmAddresses := BalanceWarm s (BalanceAddress x) } .outOfGas := by
  have pop := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  by_cases warm : BalanceAddress x ∈ s.warmAddresses <;>
    simp_all [extCodeSize, balanceAddress, BalanceAddress, BalanceWarm, BalanceCost,
      ExtCodeSizeCost, charge, Gas.charge, Nat.not_le_of_gt]

/-- An incomplete code store fails only after gas and the account read. -/
theorem extCodeSize_missing (s : State) (rest : Stack) (x : Word)
    (items : s.stack.val = x :: rest.val) (gas : ExtCodeSizeCost s (BalanceAddress x) ≤ s.gas)
    (missing : ExtCodeBytes s (BalanceAddress x) = none) :
    extCodeSize s = .exception { s with stack := rest, warmAddresses := BalanceWarm s (BalanceAddress x), tracker := BalanceRead s (BalanceAddress x), gas := s.gas - ExtCodeSizeCost s (BalanceAddress x) } .missingCode := by
  have pop := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  have addr : balanceAddress x = BalanceAddress x := rfl
  have cost : (if s.warmAddresses.contains (BalanceAddress x) then 200 else 3100) = ExtCodeSizeCost s (BalanceAddress x) := by simp [ExtCodeSizeCost, BalanceCost]; split <;> simp_all
  have warms : (if s.warmAddresses.contains (BalanceAddress x) then s.warmAddresses else BalanceAddress x :: s.warmAddresses) = BalanceWarm s (BalanceAddress x) := by simp [BalanceWarm]
  have bytes := extCodeBytes_eq s (BalanceAddress x)
  simp only [extCodeSize, pop, addr, cost, warms, charge, Gas.charge, ite_eq_left gas, bytes, missing]
  rfl

/-- An affordable successful lookup fixes all output fields. -/
theorem extCodeSize_success (s t : State) (rest : Stack) (x : Word) (code : ByteArray)
    (items : s.stack.val = x :: rest.val) (gas : ExtCodeSizeCost s (BalanceAddress x) ≤ s.gas)
    (present : ExtCodeBytes s (BalanceAddress x) = some code)
    (fields : Advances { s with warmAddresses := BalanceWarm s (BalanceAddress x), tracker := BalanceRead s (BalanceAddress x) }
      t (s.pc + 1) (s.gas - ExtCodeSizeCost s (BalanceAddress x)) (BitVec.ofNat 256 code.size :: rest.val)) :
    extCodeSize s = .continue t := by
  have pop := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  have room : rest.val.length < 1024 := by have b := s.stack.property; rw [items] at b; simp at b; omega
  let stack : Stack := ⟨BitVec.ofNat 256 code.size :: rest.val, by simp; omega⟩
  have push : rest.push (BitVec.ofNat 256 code.size) = .ok stack :=
    (Proofs.Stack.push_ok_iff _ _ _).mpr ⟨room, rfl⟩
  have eq := advances_eq { s with warmAddresses := BalanceWarm s (BalanceAddress x), tracker := BalanceRead s (BalanceAddress x) }
    t (s.pc + 1) (s.gas - ExtCodeSizeCost s (BalanceAddress x)) stack fields
  subst t
  have addr : balanceAddress x = BalanceAddress x := rfl
  have cost : (if s.warmAddresses.contains (BalanceAddress x) then 200 else 3100) = ExtCodeSizeCost s (BalanceAddress x) := by simp [ExtCodeSizeCost, BalanceCost]; split <;> simp_all
  have warms : (if s.warmAddresses.contains (BalanceAddress x) then s.warmAddresses else BalanceAddress x :: s.warmAddresses) = BalanceWarm s (BalanceAddress x) := by simp [BalanceWarm]
  have bytes := extCodeBytes_eq s (BalanceAddress x)
  simp only [extCodeSize, pop, addr, cost, warms, charge, Gas.charge, ite_eq_left gas, bytes, present, push]
  rfl

/-- Source-order EXTCODESIZE cases, independent of code and program counter. -/
inductive ExtCodeSizeLocal : State → Outcome → Prop where
  | underflow (s) : s.stack.val = [] → ExtCodeSizeLocal s (.exception s .stackUnderflow)
  | gas (s : State) (rest : Stack) (x : Word) : s.stack.val = x :: rest.val →
      s.gas < ExtCodeSizeCost s (BalanceAddress x) →
      ExtCodeSizeLocal s (.exception { s with stack := rest, warmAddresses := BalanceWarm s (BalanceAddress x) } .outOfGas)
  | missing (s : State) (rest : Stack) (x : Word) : s.stack.val = x :: rest.val →
      ExtCodeSizeCost s (BalanceAddress x) ≤ s.gas → ExtCodeBytes s (BalanceAddress x) = none →
      ExtCodeSizeLocal s (.exception { s with stack := rest, warmAddresses := BalanceWarm s (BalanceAddress x), tracker := BalanceRead s (BalanceAddress x), gas := s.gas - ExtCodeSizeCost s (BalanceAddress x) } .missingCode)
  | success (s t : State) (rest : Stack) (x : Word) (code : ByteArray) : s.stack.val = x :: rest.val →
      ExtCodeSizeCost s (BalanceAddress x) ≤ s.gas → ExtCodeBytes s (BalanceAddress x) = some code →
      Advances { s with warmAddresses := BalanceWarm s (BalanceAddress x), tracker := BalanceRead s (BalanceAddress x) }
        t (s.pc + 1) (s.gas - ExtCodeSizeCost s (BalanceAddress x)) (BitVec.ofNat 256 code.size :: rest.val) →
      ExtCodeSizeLocal s (.continue t)

/-- Every source case implies the corresponding helper outcome. -/
theorem extCodeSize_local_sound {s : State} {out : Outcome} (h : ExtCodeSizeLocal s out) : extCodeSize s = out := by
  cases h with
  | underflow empty => exact extCodeSize_underflow _ empty
  | gas rest x items gas => exact extCodeSize_gas _ rest x items gas
  | missing rest x items gas missing => exact extCodeSize_missing _ rest x items gas missing
  | success t rest x code items gas present fields => exact extCodeSize_success _ t rest x code items gas present fields

/-- The cases cover arbitrary frames, including incomplete code stores. -/
theorem extCodeSize_local_total (s : State) : ∃ out, ExtCodeSizeLocal s out := by
  cases items : s.stack.val with
  | nil => exact ⟨_, .underflow s items⟩
  | cons x xs =>
    let rest : Stack := ⟨xs, by have b := s.stack.property; rw [items] at b; simp at b; omega⟩
    have items' : s.stack.val = x :: rest.val := items
    by_cases gas : ExtCodeSizeCost s (BalanceAddress x) ≤ s.gas
    · cases bytes : ExtCodeBytes s (BalanceAddress x) with
      | none => exact ⟨_, .missing s rest x items' gas bytes⟩
      | some code =>
        let stack : Stack := ⟨BitVec.ofNat 256 code.size :: xs, by
          have b := s.stack.property; rw [items] at b; simp at b; simp; omega⟩
        let t := { s with tracker := BalanceRead s (BalanceAddress x), warmAddresses := BalanceWarm s (BalanceAddress x), stack, pc := s.pc + 1, gas := s.gas - ExtCodeSizeCost s (BalanceAddress x) }
        exact ⟨_, .success s t rest x code items' gas bytes (by simp [Advances, t, stack, rest])⟩
    · exact ⟨_, .gas s rest x items' (Nat.lt_of_not_ge gas)⟩

/-- Helper outcomes are equivalent to the independent source-order cases. -/
theorem extCodeSize_iff_local (s : State) (out : Outcome) : extCodeSize s = out ↔ ExtCodeSizeLocal s out := by
  constructor
  · intro run
    obtain ⟨result, rule⟩ := extCodeSize_local_total s
    have sound := extCodeSize_local_sound rule
    rw [run] at sound
    subst result
    exact rule
  · exact extCodeSize_local_sound

end EthLib.EVM.Frame
