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
The contract covers representation, checked natural construction and the addition result.
It does not cover all inherited BitVec operations, an interpreter, gas, stack effects or other instructions.
It makes no claim about compiled runtime correctness, cryptography or security.
The precompile modules keep their existing paths and ownership.

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

The jump destination scan belongs to iteration 04b.
Parent iteration 04 needs that scan and integration before it is complete.
This module implements no frames, gas, stack effects or instruction execution.
