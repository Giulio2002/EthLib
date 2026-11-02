module

public import EthLib.EVM.Proofs.Frame.Environment

/-! Amsterdam SLOTNUM observes a source U64 without reduction. -/

@[expose] public section
namespace EthLib.EVM.Frame

/-- A continuing SLOTNUM step pushes the exact supplied U64 value. -/
theorem slotNumber_actual (s t : State)
    (at_ : At s (some Observation.slotnum.opcode)) (run : step s = .continue t) :
    ∃ w, Word.ofNat s.context.environment.slotNumber.val = .ok w ∧
      w.toNat = s.context.environment.slotNumber.val ∧
      t.stack.val = w :: s.stack.val ∧ t.context = s.context := by
  let w := observationWord s.context.environment.slotNumber.val
  have bound : s.context.environment.slotNumber.val < Word.modulus := by
    have h := s.context.environment.slotNumber.isLt
    have widths : 2 ^ 64 < 2 ^ 256 := by decide
    simp only [Word.modulus]
    omega
  have fields := step_observation_actual s t .slotnum at_ run
  exact ⟨w, observationWord_checked _ bound, observationWord_exact _ bound,
    fields.2.2.2.2.2.2.1, fields.2.2.2.2.2.2.2.1⟩

end EthLib.EVM.Frame
