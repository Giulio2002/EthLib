import EthLib.EVM.Proofs.Frame.BlobFee
import EthLib.EVM.Proofs.Runner.BlobFee

open EthLib.EVM

example (s : Frame.State) (gas : s.gas < 2) :
    Frame.blobBaseFee s = .exception s .outOfGas := Frame.blobBaseFee_gas s gas

example (s t : Frame.State) (run : Frame.blobBaseFee s = .continue t) :
    2 ≤ s.gas ∧ s.stack.val.length < 1024 ∧
    Frame.Advances s t (s.pc + 1) (s.gas - 2)
      (Frame.observationWord (BlobFee.calculateWith s.context.environment.blobFeeSchedule s.context.environment.excessBlobGas) :: s.stack.val) :=
  Frame.blobBaseFee_helper_actual s t run

example (s t : Frame.State) (at_ : Frame.At s (some .blobbasefee))
    (run : Frame.step s = .continue t) :
    ∃ sum, BlobFee.RecurrenceSpec s.context.environment.excessBlobGas.val s.context.environment.blobFeeSchedule.updateFraction.val 1 s.context.environment.blobFeeSchedule.updateFraction.val 0 sum ∧
      2 ≤ s.gas ∧ s.stack.val.length < 1024 ∧
      Frame.Advances s t (s.pc + 1) (s.gas - 2)
        (Frame.observationWord (sum / s.context.environment.blobFeeSchedule.updateFraction.val) :: s.stack.val) :=
  Frame.blobBaseFee_actual s t at_ run

example (fuel : Nat) (s : Frame.State) (code : s.code = Runner.BlobFeeProgram.program) :
    (Runner.run fuel s).frame.memory = s.memory :=
  Runner.BlobFeeProgram.program_memory fuel s code

example (s : Frame.State) (out : Frame.Outcome) (at_ : Frame.At s (some .blobbasefee)) :
    Frame.step s = out ↔ Frame.BlobBaseFeeRule s out :=
  Frame.blobBaseFee_step_iff s out at_

example (s t : Frame.State) (gas : 2 ≤ s.gas) (room : s.stack.val.length < 1024)
    (fields : Frame.Advances s t (s.pc + 1) (s.gas - 2)
      (Frame.observationWord (BlobFee.calculateWith s.context.environment.blobFeeSchedule s.context.environment.excessBlobGas) :: s.stack.val)) :
    Frame.blobBaseFee s = .continue t :=
  Frame.blobBaseFee_success s t gas room fields

example (n d i term output result : Nat) (hd : 0 < d) (hi : 0 < i) :
    BlobFee.RecurrenceSpec n d i term output result ↔
      result = BlobFee.recurrence n d i term output hd hi :=
  BlobFee.recurrence_iff n d i term output result hd hi

example (context : CallData.Context) (returnData : ByteArray) (x : Word)
    (xs : List Word) (room : xs.length ≤ 1022) (g : Nat)
    (mem : Memory.Allocation.State) (valid : Memory.Allocation.Valid mem) :
    ∃ t, Runner.run 2 ⟨Runner.BlobFeeProgram.program, 0, ⟨x :: xs, by simp; omega⟩,
        5 + g, mem, valid, context, returnData⟩ = .exhausted t ∧
      t.stack.val = Frame.observationWord (BlobFee.calculateWith context.environment.blobFeeSchedule context.environment.excessBlobGas) ::
        Environment.blobHash context.environment x :: xs ∧
      t.context = context ∧ t.memory = mem ∧ t.returnData = returnData ∧
      t.gas = g ∧ t.pc = 2 :=
  Runner.BlobFeeProgram.run context returnData x xs room g mem valid

example (s : Frame.State) (gas : 2 ≤ s.gas) (full : s.stack.val.length = 1024) :
    Frame.blobBaseFee s = .exception s .stackOverflow :=
  Frame.blobBaseFee_full s gas full

example (factor numerator : Nat) (denominator : {d : Nat // 0 < d}) (result : Nat) :
    (∃ sum, BlobFee.RecurrenceSpec numerator denominator.val 1 (factor * denominator.val) 0 sum ∧
      result = sum / denominator.val) ↔ result = BlobFee.taylorExponential factor numerator denominator :=
  BlobFee.taylorExponential_spec factor numerator denominator result

example (excess : Fin (2 ^ 64)) (result : Nat) :
    (∃ sum, BlobFee.RecurrenceSpec excess.val 3338477 1 3338477 0 sum ∧
      result = sum / 3338477) ↔ result = BlobFee.calculateBlobGasPrice excess :=
  BlobFee.calculateBlobGasPrice_spec excess result

example (s t : Frame.State) (at_ : Frame.At s (some .blobbasefee))
    (run : Frame.step s = .continue t) :
    ∃ head, t.stack.val.head? = some head ∧
      head.toNat = BlobFee.calculateWith s.context.environment.blobFeeSchedule s.context.environment.excessBlobGas % Word.modulus :=
  Frame.blobBaseFee_step_head_mod s t at_ run

example (s t : Frame.State) (at_ : Frame.At s (some .blobbasefee))
    (run : Frame.step s = .continue t)
    (representable : BlobFee.calculateWith s.context.environment.blobFeeSchedule s.context.environment.excessBlobGas < Word.modulus) :
    ∃ head, t.stack.val.head? = some head ∧
      head.toNat = BlobFee.calculateWith s.context.environment.blobFeeSchedule s.context.environment.excessBlobGas ∧
      Word.ofNat (BlobFee.calculateWith s.context.environment.blobFeeSchedule s.context.environment.excessBlobGas) = .ok head :=
  Frame.blobBaseFee_step_head_exact s t at_ run representable
