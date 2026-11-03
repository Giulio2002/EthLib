import EthLib.EVM.Proofs.Runner.ExtCode

open EthLib.EVM

namespace ExtCodeConsumer

theorem size_underflow_forward (s : Frame.State) (empty : s.stack.val = []) :
    Frame.extCodeSize s = .exception s .stackUnderflow :=
  (Frame.extCodeSize_iff_local s _).mpr (.underflow s empty)

theorem size_gas_forward (s : Frame.State) (rest : Stack) (x : Word)
    (items : s.stack.val = x :: rest.val) (gas : s.gas < Frame.ExtCodeSizeCost s (Frame.BalanceAddress x)) :
    Frame.extCodeSize s = .exception { s with stack := rest, warmAddresses := Frame.BalanceWarm s (Frame.BalanceAddress x) } .outOfGas :=
  (Frame.extCodeSize_iff_local s _).mpr (.gas s rest x items gas)

theorem size_missing_forward (s : Frame.State) (rest : Stack) (x : Word)
    (items : s.stack.val = x :: rest.val) (gas : Frame.ExtCodeSizeCost s (Frame.BalanceAddress x) ≤ s.gas)
    (missing : Frame.ExtCodeBytes s (Frame.BalanceAddress x) = none) :
    Frame.extCodeSize s = .exception { s with stack := rest, warmAddresses := Frame.BalanceWarm s (Frame.BalanceAddress x), tracker := Frame.BalanceRead s (Frame.BalanceAddress x), gas := s.gas - Frame.ExtCodeSizeCost s (Frame.BalanceAddress x) } .missingCode :=
  (Frame.extCodeSize_iff_local s _).mpr (.missing s rest x items gas missing)

theorem size_success_forward (s t : Frame.State) (rest : Stack) (x : Word) (code : ByteArray)
    (items : s.stack.val = x :: rest.val) (gas : Frame.ExtCodeSizeCost s (Frame.BalanceAddress x) ≤ s.gas)
    (present : Frame.ExtCodeBytes s (Frame.BalanceAddress x) = some code)
    (fields : Frame.Advances { s with warmAddresses := Frame.BalanceWarm s (Frame.BalanceAddress x), tracker := Frame.BalanceRead s (Frame.BalanceAddress x) }
      t (s.pc + 1) (s.gas - Frame.ExtCodeSizeCost s (Frame.BalanceAddress x)) (BitVec.ofNat 256 code.size :: rest.val)) :
    Frame.extCodeSize s = .continue t :=
  (Frame.extCodeSize_iff_local s _).mpr (.success s t rest x code items gas present fields)

theorem size_success_converse (s t : Frame.State) (run : Frame.extCodeSize s = .continue t) :
    ∃ (rest : Stack) (x : Word) (code : ByteArray), s.stack.val = x :: rest.val ∧
      Frame.ExtCodeSizeCost s (Frame.BalanceAddress x) ≤ s.gas ∧
      Frame.ExtCodeBytes s (Frame.BalanceAddress x) = some code ∧
      Frame.Advances { s with warmAddresses := Frame.BalanceWarm s (Frame.BalanceAddress x), tracker := Frame.BalanceRead s (Frame.BalanceAddress x) }
        t (s.pc + 1) (s.gas - Frame.ExtCodeSizeCost s (Frame.BalanceAddress x)) (BitVec.ofNat 256 code.size :: rest.val) := by
  have h := (Frame.extCodeSize_iff_local s _).mp run
  cases h with
  | success _ rest x code items gas present fields => exact ⟨rest, x, code, items, gas, present, fields⟩

theorem size_missing_converse (s t : Frame.State) (run : Frame.extCodeSize s = .exception t .missingCode) :
    ∃ (rest : Stack) (x : Word), s.stack.val = x :: rest.val ∧
      Frame.ExtCodeSizeCost s (Frame.BalanceAddress x) ≤ s.gas ∧ Frame.ExtCodeBytes s (Frame.BalanceAddress x) = none ∧
      t = { s with stack := rest, warmAddresses := Frame.BalanceWarm s (Frame.BalanceAddress x), tracker := Frame.BalanceRead s (Frame.BalanceAddress x), gas := s.gas - Frame.ExtCodeSizeCost s (Frame.BalanceAddress x) } := by
  have h := (Frame.extCodeSize_iff_local s _).mp run
  cases h with
  | missing rest x items gas missing => exact ⟨rest, x, items, gas, missing, rfl⟩

theorem size_underflow_converse (s t : Frame.State) (run : Frame.extCodeSize s = .exception t .stackUnderflow) :
    s.stack.val = [] ∧ t = s := by
  have h := (Frame.extCodeSize_iff_local s _).mp run
  cases h with
  | underflow empty => exact ⟨empty, rfl⟩

theorem size_gas_converse (s t : Frame.State) (run : Frame.extCodeSize s = .exception t .outOfGas) :
    ∃ (rest : Stack) (x : Word), s.stack.val = x :: rest.val ∧ s.gas < Frame.ExtCodeSizeCost s (Frame.BalanceAddress x) ∧
      t = { s with stack := rest, warmAddresses := Frame.BalanceWarm s (Frame.BalanceAddress x) } := by
  have h := (Frame.extCodeSize_iff_local s _).mp run
  cases h with
  | gas rest x items gas => exact ⟨rest, x, items, gas, rfl⟩

theorem size_map (s : Frame.State) (a : World.Address) :
    TransactionAccount.CodeValue (TransactionState.Reference.observe s.tracker) (Frame.BalanceAccount s a).codeHash (Frame.ExtCodeBytes s a) :=
  Frame.extCodeBytes_reference s a

theorem hash_success_forward (s t : Frame.State) (rest : Stack) (x : Word)
    (items : s.stack.val = x :: rest.val) (gas : Frame.BalanceCost s (Frame.BalanceAddress x) ≤ s.gas)
    (fields : Frame.Advances { s with warmAddresses := Frame.BalanceWarm s (Frame.BalanceAddress x), tracker := Frame.BalanceRead s (Frame.BalanceAddress x) }
      t (s.pc + 1) (s.gas - Frame.BalanceCost s (Frame.BalanceAddress x)) (Frame.ExtCodeHashValue s (Frame.BalanceAddress x) :: rest.val)) :
    Frame.extCodeHash s = .continue t := (Frame.extCodeHash_success_iff s t).mpr ⟨rest, x, items, gas, fields⟩

theorem hash_success_converse (s t : Frame.State) (run : Frame.extCodeHash s = .continue t) :
    ∃ (rest : Stack) (x : Word), s.stack.val = x :: rest.val ∧ Frame.BalanceCost s (Frame.BalanceAddress x) ≤ s.gas ∧
      Frame.Advances { s with warmAddresses := Frame.BalanceWarm s (Frame.BalanceAddress x), tracker := Frame.BalanceRead s (Frame.BalanceAddress x) }
        t (s.pc + 1) (s.gas - Frame.BalanceCost s (Frame.BalanceAddress x)) (Frame.ExtCodeHashValue s (Frame.BalanceAddress x) :: rest.val) :=
  (Frame.extCodeHash_success_iff s t).mp run

theorem hash_error_converse (s t : Frame.State) (reason : Frame.Exception) (run : Frame.extCodeHash s = .exception t reason) :
    (s.stack.val = [] ∧ t = s ∧ reason = .stackUnderflow) ∨
    (∃ (rest : Stack) (x : Word), s.stack.val = x :: rest.val ∧ s.gas < Frame.BalanceCost s (Frame.BalanceAddress x) ∧
      t = { s with stack := rest, warmAddresses := Frame.BalanceWarm s (Frame.BalanceAddress x) } ∧ reason = .outOfGas) :=
  (Frame.extCodeHash_exception_iff s t reason).mp run

theorem hash_error_forward (s t : Frame.State) (reason : Frame.Exception)
    (cases_ : (s.stack.val = [] ∧ t = s ∧ reason = .stackUnderflow) ∨
      (∃ (rest : Stack) (x : Word), s.stack.val = x :: rest.val ∧ s.gas < Frame.BalanceCost s (Frame.BalanceAddress x) ∧
        t = { s with stack := rest, warmAddresses := Frame.BalanceWarm s (Frame.BalanceAddress x) } ∧ reason = .outOfGas)) :
    Frame.extCodeHash s = .exception t reason := (Frame.extCodeHash_exception_iff s t reason).mpr cases_

theorem mixed_run (xs : List Word) (room : xs.length ≤ 1022) (x : Word) (g : Nat)
    (mem : Memory.Allocation.State) (valid : Memory.Allocation.Valid mem)
    (context : CallData.Context) (returnData : ByteArray) (tracker : TransactionState.State)
    (warm : List World.Address) (slots : List (World.Address × Word)) (static : Bool) (meter : Frame.StateGas) (logs : List Frame.LogEntry)
    (cold : Frame.BalanceAddress x ∉ warm) (code : ByteArray)
    (present : Frame.ExtCodeBytes
      ⟨Runner.ExtCodeProgram.program, 0, ⟨x :: x :: xs, by simp; omega⟩, 3202 + g, mem, valid, context, returnData, tracker, warm, slots, static, meter, logs⟩
      (Frame.BalanceAddress x) = some code) :
    let s : Frame.State := ⟨Runner.ExtCodeProgram.program, 0, ⟨x :: x :: xs, by simp; omega⟩, 3202 + g,
      mem, valid, context, returnData, tracker, warm, slots, static, meter, logs⟩
    ∃ t, Runner.run 4 s = .stopped t ∧ t.pc = 4 ∧ t.gas = g ∧
      t.stack.val = Frame.ExtCodeHashValue s (Frame.BalanceAddress x) :: xs ∧
      t.tracker = { tracker with accountReads := Frame.BalanceAddress x :: Frame.BalanceAddress x :: tracker.accountReads } ∧
      t.warmAddresses = Frame.BalanceAddress x :: warm :=
  Runner.ExtCodeProgram.run xs room x g mem valid context returnData tracker warm slots static meter logs cold code present

end ExtCodeConsumer
