import EthLib.EVM.Proofs.KeccakBits

open EthLib.EVM

-- The complete sponge refinement has no link hypothesis.
example (msg : ByteArray) :
    EthLib.Cryptography.Hash.Keccak.keccak256 msg =
      EthLib.Cryptography.Hash.KeccakBits.keccak256 msg :=
  EthLib.Cryptography.Hash.KeccakBits.keccak256_eq msg

example : Frame.IndependentSpongeLink EthLib.Cryptography.Hash.KeccakBits.keccak256 :=
  Frame.independentSpongeLink_keccakBits

-- A consumer obtains the independent output from actual opcode execution.
example (s t : Frame.State) (offset length : Word) (xs : List Word)
    (at_ : Frame.At s (some .keccak)) (items : s.stack.val = offset :: length :: xs)
    (run : Frame.step s = .continue t) :
    ∃ digest, t.stack.val = digest :: xs ∧
      Word.toBytesBE digest = ⟨(EthLib.Cryptography.Hash.KeccakBits.keccak256
        ⟨(Memory.readRange s.memory.store offset.toNat length.toNat).toArray⟩).toArray⟩ := by
  obtain ⟨digest, _, stack, bytes, _⟩ :=
    Frame.keccak_step_actual_bits s t offset length xs at_ items run
  exact ⟨digest, stack, bytes⟩

-- Independent byte and bit padding agree for every message.
example (msg : ByteArray) :
    EthLib.Cryptography.Hash.KeccakBits.messageBits (EthLib.Cryptography.Hash.Keccak.pad msg) =
      EthLib.Cryptography.Hash.KeccakBits.padded msg :=
  EthLib.Cryptography.Hash.KeccakBits.paddedBits_eq msg

-- Every complete source block has the same absorption in both models.
example (a : EthLib.Cryptography.Hash.Keccak.State) (bytes : Vector UInt8 136) :
    EthLib.Cryptography.Hash.KeccakBits.ofLanes
      (EthLib.Cryptography.Hash.Keccak.Internal.absorbBlock a bytes.toList) =
    EthLib.Cryptography.Hash.KeccakBits.absorb
      (EthLib.Cryptography.Hash.KeccakBits.ofLanes a)
      (EthLib.Cryptography.Hash.KeccakBits.byteBlock bytes) :=
  EthLib.Cryptography.Hash.KeccakBits.absorbBlock_ofLanes a bytes

example (a : EthLib.Cryptography.Hash.Keccak.State) (i : Fin 32) :
    EthLib.Cryptography.Hash.KeccakBits.outputByte
      (EthLib.Cryptography.Hash.KeccakBits.ofLanes a) i.val =
    (EthLib.Cryptography.Hash.Keccak.Internal.squeeze a)[i] :=
  EthLib.Cryptography.Hash.KeccakBits.outputByte_eq_squeeze a i

-- The helper theorem also covers arbitrary code and program counters.
example (s t : Frame.State) (offset length : Word) (xs : List Word)
    (items : s.stack.val = offset :: length :: xs) (run : Frame.keccak s = .continue t) :
    ∃ digest, t.stack.val = digest :: xs ∧
      Word.toBytesBE digest = ⟨(EthLib.Cryptography.Hash.KeccakBits.keccak256
        ⟨(Memory.readRange s.memory.store offset.toNat length.toNat).toArray⟩).toArray⟩ := by
  obtain ⟨digest, _, stack, bytes, _⟩ :=
    Frame.keccak_helper_actual_bits s t offset length xs items run
  exact ⟨digest, stack, bytes⟩
