import EthLib.EVM.Proofs.Frame.Environment
import EthLib.EVM.Proofs.Runner.BlockHash

open EthLib.EVM

example (s : Frame.State) (h : List Word) (empty : s.stack.val = []) :
    Frame.blockHash s h = .exception s .stackUnderflow :=
  Frame.blockHash_empty s h empty

example (s : Frame.State) (h : List Word) (x : Word) (xs : List Word)
    (items : s.stack.val = x :: xs) (gas : s.gas < 20) :
    Frame.blockHash s h = .exception s .outOfGas :=
  Frame.blockHash_gas s h x xs items gas

example (s t : Frame.State) (h : List Word) (x : Word) (xs : List Word)
    (items : s.stack.val = x :: xs) (gas : 20 ≤ s.gas)
    (fields : Frame.Advances s t (s.pc + 1) (s.gas - 20)
      (Environment.blockHash h s.context.environment.number x :: xs)) :
    Frame.blockHash s h = .continue t :=
  Frame.blockHash_success s t h x xs items gas fields

example (s t : Frame.State) (h : List Word) (run : Frame.blockHash s h = .continue t) :
    ∃ x xs, s.stack.val = x :: xs ∧ 20 ≤ s.gas ∧
      Frame.Advances s t (s.pc + 1) (s.gas - 20)
        (Environment.blockHash h s.context.environment.number x :: xs) :=
  Frame.blockHash_actual s t h run

example (s t : Frame.State) (at_ : Frame.At s (some .blockhash))
    (run : Frame.step s = .continue t) :
    ∃ x xs, s.stack.val = x :: xs ∧ 20 ≤ s.gas ∧
      Frame.Advances s t (s.pc + 1) (s.gas - 20)
        (Environment.blockHash s.context.environment.blockHashes s.context.environment.number x :: xs) :=
  Frame.step_blockHash_actual s t at_ run

example (h : List Word) (n x : Word)
    (window : x.toNat < n.toNat ∧ n.toNat ≤ x.toNat + 256)
    (available : n.toNat - x.toNat ≤ h.length) :
    Environment.blockHash h n x = h[h.length - (n.toNat - x.toNat)]' (by omega) :=
  Environment.blockHash_in_range h n x window available

example (h : List Word) (n x : Word)
    (outside : ¬ (x.toNat < n.toNat ∧ n.toNat ≤ x.toNat + 256)) :
    Environment.blockHash h n x = 0 := Environment.blockHash_out_of_window h n x outside

example (h : List Word) (n x : Word) (missing : h.length < n.toNat - x.toNat) :
    Environment.blockHash h n x = 0 := Environment.blockHash_missing h n x missing

example (h : List Word) (n x : Word) (chain : Nat → Word)
    (valid : Environment.HistoryMatches h n chain)
    (window : x.toNat < n.toNat ∧ n.toNat ≤ x.toNat + 256) :
    Environment.blockHash h n x = chain x.toNat :=
  Environment.blockHash_source_agreement h n x chain valid window

example (s : Frame.State) (out : Frame.Outcome) : Frame.step s = out ↔ Frame.Rule s out :=
  Frame.step_iff_rule s out

example (fuel : Nat) (s : Frame.State) :
    (Runner.run fuel s).frame.context = s.context ∧
      (Runner.run fuel s).frame.returnData = s.returnData :=
  Runner.BlockHashProgram.run_preserves fuel s

example (context : CallData.Context) (ret : ByteArray) (tracker : TransactionState.State) (warmAddresses : List World.Address) (x y : Word)
    (xs : List Word) (room : xs.length ≤ 1022) (g : Nat)
    (mem : Memory.Allocation.State) (valid : Memory.Allocation.Valid mem) :
    ∃ t, Runner.run 3 ⟨Runner.BlockHashProgram.program, 0,
        ⟨x :: y :: xs, by simp; omega⟩, 43 + g, mem, valid, context, ret, tracker, warmAddresses⟩ = .exhausted t ∧
      t.stack.val = Environment.blockHash context.environment.blockHashes context.environment.number y ::
        Environment.blockHash context.environment.blockHashes context.environment.number x :: xs ∧
      t.context = context ∧ t.memory = mem ∧ t.returnData = ret ∧ t.gas = g ∧ t.pc = 3 :=
  Runner.BlockHashProgram.run context ret tracker warmAddresses x y xs room g mem valid

example (s t : Frame.State) (at_ : Frame.At s (some .blockhash))
    (run : Frame.step s = .continue t) (x : Word) (xs : List Word)
    (items : s.stack.val = x :: xs) (bytes : ByteArray)
    (window : x.toNat < s.context.environment.number.toNat ∧
      s.context.environment.number.toNat ≤ x.toNat + 256)
    (available : s.context.environment.number.toNat - x.toNat ≤ s.context.environment.blockHashes.length)
    (codec : Word.ofBytesBE bytes = .ok
      (s.context.environment.blockHashes[s.context.environment.blockHashes.length -
        (s.context.environment.number.toNat - x.toNat)]' (by omega))) :
    ∃ w, t.stack.val = w :: xs ∧ w.toBytesBE = bytes :=
  Frame.step_blockHash_codec s t at_ run x xs items bytes window available codec
