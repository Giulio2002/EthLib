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

## BYTE and SIGNEXTEND results

`Word.byte` and `Word.signextend` take the byte index first and the value second.
Both inputs are full-width words.
The index is checked before calculating a power.

The sources are Cancun execution-specs revision
[fd929841](https://github.com/ethereum/execution-specs/tree/fd9298410ec7218838c8348f69c1eb633f1797dc/src/ethereum/forks/cancun/vm/instructions),
functions `get_byte` and `signextend`, and the Shanghai Yellow Paper revision
[efc5f9a](https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex),
Appendix H.2, BYTE and SIGNEXTEND.
BYTE counts bytes from the most significant end.
SIGNEXTEND selects low bytes and copies their sign bit into the upper bits.

The proof module gives natural-number reference functions and proves equality for all word inputs.
It proves the byte bound and extraction equation, including indices at least 32.
It proves the exact unsigned sign-extension equation, low-bit preservation and upper-bit replication.
It also proves index 31 and larger are identities, idempotence, and agreement with the signed interpretation of the selected low bytes.
Boundary examples supplement these universal results.

The kernel checks refinement to the Lean reference functions.
Their correspondence to the pinned sources is a human reading of those sources.
These contracts concern result helpers only.
They do not cover byte codecs, instruction execution, gas, stack effects or compiled runtime correctness.
