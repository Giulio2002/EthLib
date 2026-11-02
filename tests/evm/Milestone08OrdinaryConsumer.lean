import EthLib.EVM

open EthLib.EVM

-- A client can execute a bounded mixed program through the ordinary import.
def runMixed (s : Frame.State) : Runner.Result := Runner.run 5 s

-- The ordinary import also exposes the operations used by the frame.
example (x y m : Word) : Word :=
  Word.bitwiseAnd (Word.addmod x y m) (Word.shl 1 (Word.eqResult x y))

example (s : Frame.State) : Frame.Outcome := Frame.step s
example (b : UInt8) : Option Opcode := Opcode.decode b
