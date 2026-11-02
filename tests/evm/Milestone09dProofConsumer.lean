import EthLib.EVM.Proofs.Runner.CopyKeccak
import EthLib.EVM.Proofs.Gas

open EthLib.EVM

example (s : Frame.State) (out : Frame.Outcome) :
    Frame.keccak s = out ↔ Frame.KeccakHelperRule s out :=
  Frame.keccak_helper_iff_rule s out

example (d : Vector UInt8 32) : Word.toBytesBE (Frame.digestWord d) = ⟨d.toArray⟩ :=
  Frame.digestWord_encode d

example (ctx : CallData.Context) (ret : ByteArray) (source : Word) (xs : List Word)
    (room : xs.length ≤ 1019) (mem : Memory.Allocation.State)
    (valid : Memory.Allocation.Valid mem) (g : Nat) :
    let bytes := CallData.readRange ctx.data source.toNat 32
    let m := Memory.Allocation.write mem 0 bytes
    let c1 := Gas.inputCopyCost mem.words 0 32
    let c2 := Gas.keccakCost m.words 0 32
    ∃ t, Runner.run 2 ⟨Runner.CopyKeccak.program, 0,
        ⟨[0, source, 32, 0, 32] ++ xs, by simp; omega⟩,
        c1 + c2 + g, mem, valid, ctx, ret⟩ = .exhausted t ∧
      t.stack.val = Frame.digestWord (EthLib.Cryptography.Hash.Keccak.keccak256 ⟨bytes.toArray⟩) :: xs ∧
      t.pc = 2 ∧ t.gas = g ∧ t.memory.store = m.store ∧ t.context = ctx ∧
      t.returnData = ret ∧ Memory.readRange t.memory.store 0 32 = bytes :=
  Runner.CopyKeccak.run_copy_keccak ctx ret source xs room mem valid g

-- The rounded count is specified by coverage bounds, independently of division.
example (old offset length cost : Nat) :
    Gas.keccakCost old offset length = cost ↔
      ∃ words, Gas.RoundedHashWords length words ∧
        cost = 30 + 6 * words + Gas.rangeCost old offset length :=
  Gas.keccakCost_spec old offset length cost

example (old offset : Nat) : Gas.keccakCost old offset 0 = 30 :=
  Gas.keccakCost_zero old offset

example (old offset length : Nat) :
    old ≤ max old (Memory.Allocation.requiredWords offset length) ∧
    Gas.memoryCost old + Gas.keccakCost old offset length =
      Gas.memoryCost (max old (Memory.Allocation.requiredWords offset length)) +
        30 + 6 * ((length + 31) / 32) :=
  Gas.keccakCost_expansion old offset length

-- No condition on code or PC is needed for a helper consumer.
example (s t : Frame.State) (offset length : Word) (xs : List Word)
    (items : s.stack.val = offset :: length :: xs) (run : Frame.keccak s = .continue t) :
    ∃ digest, t.stack.val = digest :: xs ∧
      Word.toBytesBE digest = ⟨(EthLib.Cryptography.Hash.Keccak.keccak256
        ⟨(Memory.readRange s.memory.store offset.toNat length.toNat).toArray⟩).toArray⟩ ∧
      t.pc = s.pc + 1 := by
  obtain ⟨digest, _, stack, bytes, _, _, pc, _⟩ :=
    Frame.keccak_helper_actual_output s t offset length xs items run
  exact ⟨digest, stack, bytes, pc⟩

example (s t : Frame.State) (offset length : Word) (xs : List Word)
    (at_ : Frame.At s (some .keccak)) (items : s.stack.val = offset :: length :: xs)
    (run : Frame.step s = .continue t) :
    ∃ digest, t.stack.val = digest :: xs ∧
      Word.toBytesBE digest = ⟨(EthLib.Cryptography.Hash.Keccak.keccak256
        ⟨(Memory.readRange s.memory.store offset.toNat length.toNat).toArray⟩).toArray⟩ ∧
      t.memory.words = max s.memory.words (Memory.Allocation.requiredWords offset.toNat length.toNat) := by
  obtain ⟨digest, _, stack, bytes, words, _⟩ :=
    Frame.keccak_step_actual_output s t offset length xs at_ items run
  exact ⟨digest, stack, bytes, words⟩
