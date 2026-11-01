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
The contract covers representation, checked natural construction and addition.
The sections below cover further word result contracts.
It does not cover all inherited BitVec operations, an interpreter, gas, stack effects or other instructions.
It makes no claim about compiled runtime correctness, cryptography or security.
The precompile modules keep their existing paths and ownership.

## Unsigned division and remainder

The first argument is the first-popped numerator.
The second argument is the divisor.
The Yellow Paper Appendix H.2 DIV and MOD equations return zero for a zero divisor.
For a nonzero divisor they give the natural quotient and remainder.
The pinned Cancun execution specification agrees with this order and zero case.
Its source is [arithmetic.py at fd92984](https://github.com/ethereum/execution-specs/blob/fd9298410ec7218838c8348f69c1eb633f1797dc/src/ethereum/forks/cancun/vm/instructions/arithmetic.py).

`Word.div` and `Word.mod` implement those result equations.
`Reference.div` and `Reference.mod` model bounded natural values independently.
The proofs establish both numeric equations and refinement for every pair of words.
They also establish range, the remainder bound and quotient-remainder decomposition.
The latter two laws assume a nonzero divisor.
These helpers do not model instruction execution, stack effects or gas.

## Signed division and remainder

The Shanghai Yellow Paper revision linked above specifies SDIV and SMOD in Appendix H.2.
The Cancun execution specification revision [fd92984](https://github.com/ethereum/execution-specs/blob/fd9298410ec7218838c8348f69c1eb633f1797dc/src/ethereum/forks/cancun/vm/instructions/arithmetic.py) gives the same result rules in `sdiv` and `smod`.
The first operand is the first popped word and is the numerator.
The second operand is the divisor.

`Word.signed` interprets each word as a signed two's-complement integer.
`Word.ofSigned` accepts any integer and wraps it modulo `2^256`.
Unlike `Word.ofNat`, it does not reject out-of-range inputs.
The `signed_ofSigned` theorem gives its signed result for every integer using balanced remainder.
`Word.sdiv` truncates the quotient toward zero.
`Word.smod` gives the remainder the numerator's sign.
Both return zero for a zero divisor.
The signed minimum divided by -1 returns the signed minimum word.

`EthLib.EVM.Proofs.Word.SignedDivMod.Reference` defines integer quotient and remainder using natural magnitudes and signs.
The kernel checks refinement for every pair of words, including zero divisors and overflow.
The proofs also establish signed range and representation round trips, the remainder sign and magnitude, and the quotient and remainder identity outside the overflow case.
The machine-checked result is refinement to this Lean model.
Correspondence between the model and the cited sources is a human interpretation.
These helpers do not execute instructions or model the stack, gas, or an interpreter.
They make no claim about compiled runtime correctness or security.

# Comparison results

The Cancun execution specification revision [fd92984](https://github.com/ethereum/execution-specs/blob/fd9298410ec7218838c8348f69c1eb633f1797dc/src/ethereum/forks/cancun/vm/instructions/comparison.py) defines the comparison results.
The Yellow Paper revision linked above gives the same equations in Appendix H.2.
The left operand is the first popped word.
Each helper returns 1 when its condition holds and 0 otherwise.

`Word.ltResult` and `Word.gtResult` compare unsigned natural values.
`Word.sltResult` and `Word.sgtResult` compare `Word.signed` integer values.
`Word.eqResult` and `Word.iszeroResult` test equality and zero.
The separate proof module establishes exact equations, result bounds, predicate equivalences, and ordering identities for all operands.
The kernel checks refinement to these Lean mathematical predicates.
Correspondence with the cited sources is a human interpretation.
The helpers do not model instruction execution, stack effects, gas, or an interpreter.

# Shift results

The Cancun execution specification revision [fd92984](https://github.com/ethereum/execution-specs/blob/fd9298410ec7218838c8348f69c1eb633f1797dc/src/ethereum/forks/cancun/vm/instructions/bitwise.py) gives `bitwise_shl`, `bitwise_shr` and `bitwise_sar`.
The Yellow Paper revision linked above gives SHL, SHR and SAR in Appendix H.2.
[EIP-145, Specification](https://eips.ethereum.org/EIPS/eip-145#specification), gives their arithmetic equations.
The shift count is the first popped word and the value is the second.
The helpers take the full unsigned count.
They guard counts at least 256 before computing powers.
For such counts, SHL and SHR return zero.
SAR returns the all-ones word for a negative value and zero otherwise.
For smaller counts, SAR divides the signed value and rounds down.

The kernel checks the piecewise equations, signed quotient range, sign preservation and zero-shift identities for all words.
Boundary examples supplement those contracts.
The correspondence between the Lean equations and the sources is a human interpretation.
These helpers give word results only and do not model opcode execution, gas or stack effects.

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
