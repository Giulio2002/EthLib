import EthLib.EVM

open EthLib.EVM

-- A client can execute a bounded mixed program through the ordinary import.
def runMixed (s : Frame.State) : Runner.Result := Runner.run 5 s

-- The ordinary import also exposes the operations used by the frame.
example (x y m : Word) : Word :=
  Word.bitwiseAnd (Word.addmod x y m) (Word.shl 1 (Word.eqResult x y))

example (s : Frame.State) : Frame.Outcome := Frame.step s
example (b : UInt8) : Option Opcode := Opcode.decode b

-- A client using only the ordinary import can execute a zero-length MCOPY.
example : match Frame.step ⟨⟨#[0x5e]⟩, 0, ⟨[0, 0, 0], by decide⟩, 3,
    Memory.Allocation.empty, by intro a _h; rfl⟩ with
  | .continue t => t.gas = 0 ∧ t.memory.words = 0
  | _ => False := by cbv

-- The ordinary import derives the copy allocation from an observed successful step.
example (s t : Frame.State) (x y z : Word) (a b rest : Stack)
    (at_ : Frame.At s (some .mcopy)) (p1 : s.stack.pop = .ok (x, a))
    (p2 : a.pop = .ok (y, b)) (p3 : b.pop = .ok (z, rest))
    (run : Frame.step s = .continue t) :
    t.memory = Memory.Allocation.copy s.memory x.toNat y.toNat z.toNat ∧
    t.code = s.code := by
  have fields := (Frame.mcopy_actual_fields s t x y z a b rest at_ p1 p2 p3 run).2
  exact ⟨fields.2.1, fields.1⟩
