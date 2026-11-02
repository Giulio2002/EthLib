import EthLib.EVM.Proofs.Frame.BlobFee
import EthLib.EVM.Proofs.Runner.BlobFee

open EthLib.EVM

example (excess : Fin (2 ^ 64)) :
    BlobFee.calculateBlobGasPrice excess = BlobFee.calculateWith BlobFee.cancun excess :=
  BlobFee.calculateBlobGasPrice_cancun excess

example (s t : Frame.State) (at_ : Frame.At s (some .blobbasefee))
    (run : Frame.step s = .continue t) :
    ∃ head, t.stack.val.head? = some head ∧
      head.toNat = BlobFee.calculateWith s.context.environment.blobFeeSchedule
        s.context.environment.excessBlobGas % Word.modulus :=
  Frame.blobBaseFee_step_head_mod s t at_ run

example (s : Frame.State) (out : Frame.Outcome)
    (at_ : Frame.At s (some .blobbasefee)) :
    Frame.step s = out ↔ Frame.BlobBaseFeeRule s out :=
  Frame.blobBaseFee_step_iff s out at_
