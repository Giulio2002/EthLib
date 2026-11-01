module

public import EthLib.EVM.Proofs.Word
public import EthLib.EVM.Proofs.Word.DivMod
public import EthLib.EVM.Proofs.Word.SignedDivMod
public import EthLib.EVM.Proofs.Word.Comparisons
public import EthLib.EVM.Proofs.Word.Bitwise
public import EthLib.EVM.Proofs.Word.Shifts
public import EthLib.EVM.Proofs.Word.ByteSignExtend
public import EthLib.EVM.Proofs.Word.AddMulMod
public import EthLib.EVM.Proofs.Word.Exp

/-!
# `EthLib.EVM.Proofs`

Word representation, range, and strict construction contracts.
Arithmetic, comparison, bitwise, BYTE and SIGNEXTEND result contracts.
Division and remainder contracts cover signed and unsigned results.
Arithmetic contracts include modular addition and exponentiation.
This root belongs to the separate `Proofs` library.
-/
