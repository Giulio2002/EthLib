# Word correctness contract

`Word` is an abbreviation for `BitVec 256`.
Its constructors, literals and operators remain available.
The checked input policy applies only to `Word.ofNat`.

The source is the [Shanghai Yellow Paper, revision efc5f9a](https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex).
Section 9.1 specifies 256-bit words.
Appendix H.2's arithmetic preamble and ADD result equation specify addition modulo `2^256`.
Checked natural construction is a library boundary policy, not an EVM instruction.

`EthLib.EVM.Proofs.Word.Reference.Value` models naturals below `2^256`.
Its addition uses natural addition followed by remainder modulo `2^256`.
Its constructor checks the bound independently of the executable API.

The kernel checks these contracts for all inputs:

- `decode_encode` and `encode_decode` give both representation round trips.
- `decode_injective` and `decode_surjective` establish a bijection with bounded naturals.
- `ofNat_ok_iff` characterizes success by the bound and the exact returned natural value.
- `ofNat_success_iff` states that some successful result exists exactly for in-range input.
- `ofNat_error_iff` characterizes rejection exactly by `2^256 <= n`.
- `ofNat_toNat` checks every word's observed value back into the same word.
- `ofNat_refines` equates checked construction with the reference model, including errors.
- `toNat_add` and `add_refines` establish modular addition for every pair of words.
- `toNat_lt`, `add_lt` and `modulus_pos` establish the required bounds.
- `add_no_wrap` and `add_wrap` give the two carry cases without restricting operand values further.

The existing commutativity, associativity and zero identity proofs supply algebraic laws.
Boundary examples supplement these universal statements.
They do not establish the contract by themselves.

The machine-checked claim is refinement to this Lean mathematical model.
Correspondence between that model and the cited paper is a human reading of the source.
The contract covers representation, checked natural construction and the addition, unsigned division and unsigned remainder results.
It does not cover all inherited BitVec operations, an interpreter, gas, stack effects or other instructions.
It makes no claim about compiled runtime correctness, cryptography or security.
The precompile modules keep their existing paths and ownership.

## EXP result

Cancun execution-specs `exp` at revision `fd9298410ec7218838c8348f69c1eb633f1797dc` pops the base first and exponent second.
The operation computes the power modulo `2^256`.
The Yellow Paper Appendix H.2 gives the same result.
`Word.exp` uses the MODEXP square-and-multiply algorithm with the entire word exponent.
Its proof establishes the natural result, bounded reference refinement, corner cases and the 256-bit step bound.
The correspondence between the sources and this model is a human interpretation.
The Lean proofs concern the result, not opcode gas, stack or interpreter behavior.

## Subtraction, multiplication and bitwise results

`Word.sub` and `Word.mul` reduce their results modulo `2^256`.
`Word.bitwiseAnd`, `Word.bitwiseOr`, `Word.bitwiseXor` and `Word.bitwiseNot` operate on all 256 bits.
The Yellow Paper Appendix H.2 gives SUB, MUL, AND, OR, XOR and NOT.
The separate proofs establish arithmetic refinement and bitwise equations for all inputs.

## Big-endian word codecs

`Word.toBytesBE` encodes exactly 32 bytes in most-significant-byte-first order.
`Word.ofBytesBE` rejects every other length.
The proofs establish both round trips, exact length, byte positions and injectivity.
The length check is a library boundary and does not model EVM memory padding.

The codec reuses byte conversion from MODEXP, and EXP reuses its modular arithmetic.
Neither uses the precompile's later-fork gas rules or input size restrictions.
The current EXP import of `Modexp.Core` does transitively import its gas module; only `powMod` is called.
The precompile remains in its existing domain, and shared cryptography remains separate.
