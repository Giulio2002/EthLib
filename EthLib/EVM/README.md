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

## EXP result

Cancun execution-specs `exp` at revision `fd9298410ec7218838c8348f69c1eb633f1797dc` pops the base first and exponent second.
The operation computes the power modulo `2^256`.
The Yellow Paper Appendix H.2 gives the same result.
`Word.exp` uses the MODEXP square-and-multiply algorithm with the entire word exponent.
Its proof establishes the natural result, bounded reference refinement, corner cases and the 256-bit step bound.
The correspondence between the sources and this model is a human interpretation.
The frame contracts below cover the instruction as well as this result helper.

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
The precompile belongs to the Execution domain, and shared cryptography remains separate.

# Cancun opcode decoding

`Opcode` represents the assigned Cancun opcode bytes.
PUSH lengths and DUP, SWAP and LOG indices are bounded in the type.
DUP and SWAP indices start at zero, so index zero denotes DUP1 or SWAP1.
`INVALID` is a designated instruction at `0xfe`.
The decoder returns `none` for unassigned bytes.
Classification does not mean instruction execution is implemented.

The source is execution-specs revision `fd9298410ec7218838c8348f69c1eb633f1797dc`.
The Cancun `vm.instructions.Ops` enum and `op_implementation` give the byte assignments.
The Shanghai Yellow Paper revision `efc5f9a1f356cba376c978eedb63cb0363c2aa85`, Appendix H.2, names `INVALID`.
The EELS enum omits that byte from its dispatch.
Cancun adds BLOBHASH, BLOBBASEFEE, TLOAD, TSTORE and MCOPY to the Shanghai table.

The proof module independently lists byte and constructor pairs from those sources.
It proves equality with the decoder for every byte and both encoding round trips.
The kernel checks the proof; the source transcription is a human review.

`PushImmediate` reads the length from a PUSH constructor.
It pads missing bytes on the right and interprets the result as a big-endian word.
Its natural-number program counter does not wrap.
Execution-specs Cancun `vm.instructions.stack.push_n` and `vm.memory.buffer_read` specify the read, padding and advance.
The arbitrary natural offset extends the source's bounded offset representation.
The proofs cover each byte, the length, the exact numeric value, padding and PUSH0.

The opcode and PUSH modules implement no frames, gas, stack effects or instruction execution.

# Jump destination scan

The scanner uses the Cancun `vm.runtime.get_valid_jump_destinations` rule at revision `fd9298410ec7218838c8348f69c1eb633f1797dc`.
The Shanghai Yellow Paper revision `efc5f9a1f356cba376c978eedb63cb0363c2aa85`, section 9.4.3, gives the same boundary rule.
It scans the entire code and skips PUSH1 through PUSH32 data.
PUSH0 has no data.
The scan continues past all other bytes, including unassigned bytes.
Its program counters use natural arithmetic.

The proof defines instruction boundaries independently from the scanner using source byte lengths.
The kernel checks that membership is exactly a boundary containing byte `0x5b`.
It also checks strict ordering, bounds, progress and agreement of the decoder step with the byte ranges.
The correspondence between that Lean relation and the source is a human source review.

The jump destination scan belongs to iteration 04b.
The combined opcode decoder, PUSH immediate reader and jump destination scanner pass their library, proof and standalone test gates.
This completes the scoped decoding milestone, not EVM execution or EELS differential validation.
Parent iteration 04 remains incomplete until integration, its child gates and combined tests pass.
The decoder and scanner do not model frames, gas, stack effects or instruction execution.

# Restricted frame execution

The frame runner supports STOP, PUSH0 through PUSH32, POP, ADD, MUL, SUB, DIV, MOD, SDIV, SMOD, ADDMOD, MULMOD, EXP, LT, GT, SLT, SGT, EQ, ISZERO, AND, OR, XOR, NOT, SHL, SHR, SAR, BYTE, SIGNEXTEND, DUP1 through DUP16, and SWAP1 through SWAP16.
The arithmetic, comparison and bitwise instructions have independent success, underflow and out-of-gas rules.
Operand checks precede charging gas.
ADDMOD and MULMOD pop their modulus third and use full-precision intermediates.
EXP pops its base first and its exponent second.
For shifts and byte operations, the first-popped word is the count or index.
BYTE indexes from the most significant byte.
SAR rounds a negative quotient down.
Their numeric refinement theorems compose the instruction rules with the existing word contracts.
Other assigned Cancun opcodes return a distinct unsupported tooling result.
Unassigned bytes and INVALID cause exceptional halts.
Fuel exhaustion is a tooling result and is not an EVM exception.
The frame holds code, a natural program counter, a bounded stack, gas, and valid allocated memory.
It does not execute REVERT or model world state, calls, or rollback.
A manually constructed revert carries remaining gas and output bytes as scaffolding.
The restricted step and runner cannot produce that constructor for any input or fuel.
World-state rollback and REVERT execution belong to milestone 12.
Exhaustive matches on `Frame.Outcome`, `Runner.Result`, or `Frame.Boundary` must handle the new revert constructor.

The source is Cancun execution-specs revision `fd9298410ec7218838c8348f69c1eb633f1797dc`.
`vm/instructions/control_flow.py`, `stop`, increments the program counter.
For `PUSH1 2; PUSH1 3; ADD; STOP` starting at zero, the final program counter is six.
The STOP byte is at position five.
This corrects any example that treats the STOP position as the final counter.
Reaching the end of code without executing STOP leaves the counter unchanged.

The exception result retains the input frame for diagnostics only.
`Frame.settle` projects zero remaining gas for every exception.
It does not assert a final stack or model world-state rollback.
The independent `Frame.Rule` relation states the instruction cases using stack lists and gas conditions.
The kernel checks `step_iff_rule` for all frames and outcomes.
Runner terminal trace adequacy uses this relation and sufficient fuel.
The source transcription is a human reading of the cited Python, not an automatically checked equivalence to it.

`Runner.StraightLine.push_push_add_stop` proves the example for any two immediate bytes.
It assumes at most 1022 initial stack entries and gas `9 + g`.
The result leaves the modular sum above the original stack, retains gas `g`, and stops at counter six.
`Runner.StraightLine.two_plus_three` specializes it to an empty stack and gas nine.

## EXP gas

`Gas.expBytes` counts the bytes in the shortest unsigned encoding of an exponent.
`Gas.expCost` charges 10 gas plus 50 gas for each such byte.
The source is Cancun execution-specs revision `fd9298410ec7218838c8348f69c1eb633f1797dc`.
The rules appear in `vm/instructions/arithmetic.py`, `exp`, and `vm/gas.py`, `GasCosts`.

The proof characterizes the byte count using powers of two and proves it is unique.
It also bounds the byte count by 32 and the cost by 1610.
The EXP frame rule charges this cost after both stack checks.
