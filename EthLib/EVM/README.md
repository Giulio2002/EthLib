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
Correspondence between that model and the cited paper is a manual reading of the source.
The contract covers representation, checked natural construction and addition.
The sections below cover further word result contracts.
It does not cover all inherited BitVec operations, an interpreter, gas, stack effects or other instructions.
It makes no claim about compiled runtime correctness, cryptography or security.
The precompile modules keep their existing paths and ownership.

# Byte contents contract

The sparse store models byte contents independently of allocated memory size.
The source is Cancun execution-specs revision `fd9298410ec7218838c8348f69c1eb633f1797dc`, `vm/memory.py`, functions `memory_write` and `memory_read_bytes`.
Those functions access an allocated bytearray.
Interpreting unallocated addresses as zero in a total function is this module's abstraction, not a claim that the source reads outside the bytearray.
Allocation and ranges are modeled by separate modules.
Gas and instructions remain outside this contract.

Every finite list of address and byte pairs is a valid store.
The first occurrence of an address determines its byte, and an absent address reads zero.
A write adds one pair, including for zero, so it does not allocate up to the address.
The finite support list contains every address whose observed byte is nonzero, but may also contain zero and shadowed writes.
It is not the logical memory size.

The kernel checks that empty reads zero, a write changes exactly its address, and support remains finite.
It checks overwrite, write-back and commutation for distinct addresses as equality of total observed byte functions.
These equalities do not assert equality of write histories.
The source interpretation is a manual reading; the proofs establish refinement to the stated Lean abstraction.
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
Correspondence between the model and the cited sources is a manual interpretation.
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
Correspondence with the cited sources is a manual interpretation.
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
The correspondence between the Lean equations and the sources is a manual interpretation.
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
Their correspondence to the pinned sources is a manual reading of those sources.
These contracts concern result helpers only.
They do not cover byte codecs, instruction execution, gas, stack effects or compiled runtime correctness.

## Modular addition and multiplication

`Word.addmod` and `Word.mulmod` model the ADDMOD and MULMOD results.
The first two arguments are arithmetic operands and the third is the modulus.
The sum or product is formed in natural numbers before reduction.
A zero modulus gives zero.

The sources are Cancun execution-specs revision `fd9298410ec7218838c8348f69c1eb633f1797dc`,
`vm/instructions/arithmetic.py`, functions `addmod` and `mulmod`, and the cited
Yellow Paper Appendix H.2 ADDMOD and MULMOD equations.
The proof module gives independent natural-number reference equations, bounds,
commutativity, identities and invariance under reducing the operands first.
The exact equations have no residual reduction modulo `2^256`.
Boundary examples include carries and high product bits.

The source-to-model correspondence is a manual interpretation of these sources.
The kernel checks refinement of the word results to that model.
These helpers make no claim about opcode execution, gas, stack or runtime behavior.

## EXP result

Cancun execution-specs `exp` at revision `fd9298410ec7218838c8348f69c1eb633f1797dc` pops the base first and exponent second.
The operation computes the power modulo `2^256`.
The Yellow Paper Appendix H.2 gives the same result.
`Word.exp` uses the MODEXP square-and-multiply algorithm with the entire word exponent.
Its proof establishes the natural result, bounded reference refinement, corner cases and the 256-bit step bound.
The correspondence between the sources and this model is a manual interpretation.
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
The precompile remains in its existing domain, and shared cryptography remains separate.


# Logical memory and word access

`Memory.Allocation.State` tracks allocated 32-byte words separately from sparse contents.
Range reads and writes expand this allocation to cover their nonempty ranges.
Copies expand both ranges and read a snapshot before writing.
The allocation proofs establish exact sizes and preservation of `Valid`.

The Cancun execution specification revision [fd92984](https://github.com/ethereum/execution-specs/blob/fd9298410ec7218838c8348f69c1eb633f1797dc/src/ethereum/forks/cancun/vm/instructions/memory.py) defines `mload`, `mstore` and `mstore8`.
`loadWord` reads 32 bytes in big-endian order and returns the expanded state.
`storeWord` writes the 32-byte word encoding.
`storeByte` writes the low byte.
Natural addresses do not wrap.
These helpers model memory contents and allocation, not opcode execution, gas, stack or errors.
The separate proofs establish the numeric load, byte positions, round trip, allocation and validity laws.
They also establish preservation outside writes, disjoint reads and copy-then-load consistency.

The frame executes Cancun `mcopy` by popping destination, source and length.
It charges the base, rounded copy words and expansion for both ranges before copying.
The copy reads the input snapshot, so overlapping ranges work in either direction.
Empty ranges do not expand memory, even at the largest word offset.
The frame proofs derive the exact gas, allocation and byte observations from a successful step.
`PureMemoryStep` excludes `calldatacopy`, `codecopy`, `returndatacopy`, `mcopy`, and the other memory instructions.

A load entirely beyond valid allocation returns zero.
For any prefix length `k <= 32`, a load whose remaining bytes are outside allocation
is the prefix value multiplied by `256^(32-k)`.
Disjoint word and byte stores commute as byte observations and allocated word counts.
Their sparse write histories need not be equal.

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
The kernel checks the proof against the transcribed table.
Agent source inspection is not human approval or a proof of equivalence to Python.

`PushImmediate` reads the length from a PUSH constructor.
It pads missing bytes on the right and interprets the result as a big-endian word.
Its natural-number program counter does not wrap.
Execution-specs Cancun `vm.instructions.stack.push_n` and `vm.memory.buffer_read` specify the read, padding and advance.
The arbitrary natural offset extends the source's bounded offset representation.
The proofs cover each byte, the length, the exact numeric value, padding and PUSH0.

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
The correspondence between that Lean relation and the source is a manual source inspection.

The combined opcode decoder, PUSH immediate reader and jump destination scanner pass their library, proof and standalone test gates.
This completes the scoped decoding milestone, not EVM execution or EELS differential validation.
The decoder and scanner do not model frames, gas, stack effects or instruction execution.

# Restricted frame execution

The frame runner supports STOP, JUMP, JUMPI, JUMPDEST, PC, MSIZE, GAS, MLOAD, MSTORE, MSTORE8, MCOPY, CALLDATALOAD, CALLDATASIZE, CALLDATACOPY, CODESIZE, CODECOPY, PUSH0 through PUSH32, POP, arithmetic, comparison and bitwise instructions, DUP1 through DUP16, and SWAP1 through SWAP16.
The implemented arithmetic and bitwise instructions are ADD, MUL, SUB, DIV, MOD, SDIV, SMOD, ADDMOD, MULMOD, EXP, LT, GT, SLT, SGT, EQ, ISZERO, AND, OR, XOR, NOT, SHL, SHR, SAR, BYTE and SIGNEXTEND.
The arithmetic, comparison and bitwise instructions have independent success, underflow and out-of-gas rules.
Operand checks precede charging gas.
ADDMOD and MULMOD pop their modulus third and use full-precision intermediates.
EXP pops its base first and its exponent second.
For shifts and byte operations, the first-popped word is the count or index.
BYTE indexes from the most significant byte.
SAR rounds a negative quotient down.
Their numeric refinement theorems compose the instruction rules with the existing word contracts.
JUMP and JUMPI pop the full 256-bit destination before charging gas.
JUMPI pops its condition second and checks the destination only when that condition is nonzero.
A taken jump requires a JUMPDEST at an instruction boundary, outside PUSH data.
An invalid destination has its own exceptional-halt reason.
JUMPDEST charges one gas and advances one byte.
PC, MSIZE and GAS charge two gas before checking stack capacity.
PC pushes the current counter, MSIZE pushes allocated bytes, and GAS pushes the gas remaining after its own charge.
The frame uses unbounded natural numbers for these values.
The observation conversion reduces them modulo 2^256 outside the source U256 domain.
Within that domain the conversion is exact.
CALLDATALOAD pops the full offset before charging three gas.
It reads 32 bytes from the immutable message input in big-endian order.
Missing bytes are zero on the right, and the read does not expand memory.
CALLDATASIZE and CODESIZE charge two gas before pushing their sizes.
CODESIZE observes the executing frame code, not the message input.
The source constructs U256 from these lengths, so exact agreement requires a length below 2^256.
For larger natural lengths the frame uses its proved modulo extension.

`Frame.State` requires a `CallData.Context` followed by a `ByteArray` return-data buffer.
Clients must supply both inputs explicitly.
The return-data buffer belongs to the frame and is distinct from immutable message input.
Every supported step and bounded outcome preserves both fields.
The straight-line, mixed, calldata and store-load program theorems take arbitrary values for both.

The `Advances` and `AdvancesMemory` predicates include return-data equality.
Proof consumers constructing these predicates must provide that equality.
`PureMemoryStep` excludes RETURNDATACOPY.
`Observation` includes `returndatasize`.
Exhaustive matches on `Frame.Exception` must handle `outOfBoundsRead`.
`Frame.returnDataCopy` is a public helper over any frame, independent of code and program counter.
`returnDataCopy_helper_iff_rule` characterizes its stack, gas, bounds and success outcomes.
The helper's actual-success and output theorems derive its fields and bytes from execution.

RETURNDATASIZE charges two gas before checking stack capacity.
It observes the return-data buffer and uses the same total modulo conversion as other size observations.
The conversion agrees exactly with the source U256 value when the buffer size is less than 2^256.

RETURNDATACOPY pops destination, source and length before charging gas.
The charge covers rounded copy words and destination memory expansion.
The source bound is checked after the charge using natural addition.
A range past the end raises `outOfBoundsRead` without changing diagnostic memory.
An empty range at the end succeeds, while an empty range beyond it fails.
A successful copy writes the exact source bytes and preserves memory outside the destination.
The copy-then-load program theorem quantifies over buffers with explicit gas and source-bound premises.
The frame does not execute calls or creates that change the buffer.

MLOAD reads a 32-byte big-endian word and expands memory.
MSTORE writes 32 big-endian bytes, and MSTORE8 writes the low byte.
Each pops the full 256-bit offset before gas is charged.
Expansion uses natural-number addresses and costs, without wrapping the end address.
Memory contents are sparse, so expansion does not materialize zero bytes.
Gas, allocation and program counters are natural numbers in this model.
Values outside the source types' domains are total extensions of the source.
Other assigned Cancun opcodes return a distinct unsupported tooling result.
Unassigned bytes and INVALID cause exceptional halts.
Fuel exhaustion is a tooling result and is not an EVM exception.
The runner is fuel bounded and makes no claim that every program terminates.
The frame holds code, a natural program counter, a bounded stack, gas, valid allocated memory, immutable message input, and return data.
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

`Frame.continue_unchanged`, `Frame.outcome_unchanged`, and `Runner.run_unchanged` no longer hold for memory instructions.
Use `Frame.continue_code_unchanged`, `Frame.outcome_code_unchanged`, and `Runner.run_code_unchanged` for code preservation.
For memory preservation, use `Frame.continue_memory_unchanged_of_pure`, `Frame.outcome_memory_unchanged_of_pure`, or `Runner.run_memory_unchanged_of_pure` with the stated pure-step or pure-trace premise.
The `Frame.mload_success_output`, `Frame.mstore_success_output`, and `Frame.mstore8_success_output` theorems derive output facts from an observed successful step.

The exception result retains the input frame for diagnostics only.
`Frame.settle` projects zero remaining gas for every exception.
It does not assert a final stack or model world-state rollback.
The independent `Frame.Rule` relation states the instruction cases using stack lists and gas conditions.
The kernel checks `step_iff_rule` for all frames and outcomes.
Runner terminal trace adequacy uses this relation and sufficient fuel.
An agent inspected the source transcription against the cited Python.
That inspection is not human approval or an automatically checked equivalence.

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

The milestone 08 instruction subset has source-shaped rules for each supported opcode.
The kernel checks those rules against the executable step for every frame.
The bounded runner composes the rules without treating fuel as protocol gas.
`Runner.Mixed.add_iszero_pc_gas` proves a program with arithmetic, comparison and observations.
Its GAS result reduces modulo 2^256 for every natural gas reserve.
The result is exact when that reserve is below 2^256.

The integration audit covers this restricted subset and its stated source-domain bounds.
An agent inspected the pinned sources; that inspection is not human approval or a Python-to-Lean proof.

## Input copying (09c2)

CALLDATACOPY reads the immutable message input.
CODECOPY reads the executing frame code.
Each pops destination, source and length before charging gas.
The charge covers the rounded length and destination expansion.
The source never expands memory.
Bytes beyond the source are zero.
An empty copy leaves memory unchanged at any offsets.

`CallData.readRange` accepts natural offsets and lengths.
It builds exactly the requested number of bytes.
Callers must check gas before requesting a potentially large range.
Frame operands are 256-bit words and range arithmetic uses natural numbers.
The helper also accepts natural numbers outside the source word domain.

`Frame.inputCopy_helper_success_output` applies to any byte array and any frame counter.
It derives bytes and preserved fields from a successful helper call.
`Frame.inputCopy_success_output` derives the same facts from a successful step.
`Frame.inputCopy_then_mload_actual` relates a 32-byte copy and a following load.
`Frame.inputCopy_then_mload_program` constructs both steps from code and gas premises.
`PureMemoryStep` now excludes both input-copy instructions.
Consumers constructing a pure-step proof must establish those extra exclusions.
The independent rules include both instructions and `step_iff_rule` remains unconditional.
The pinned source review is manual and does not prove Python-to-Lean equivalence.

The milestone 09c integration proof `Runner.MixedCopy.run_mixed` executes five instructions.
CALLDATACOPY writes 32 bytes at offset 0 and RETURNDATACOPY writes 32 bytes at offset 32.
Two MLOAD instructions observe those ranges, with SWAP1 between them.
The theorem takes arbitrary valid initial memory and computes each expansion charge from it.
It requires the return-data source range to contain 32 bytes.
Calldata reads use zero padding, so they need no source bound.
The theorem gives the stack, gas, program counter, bytes, and preserved frame inputs.
It also proves that bytes at offsets 64 and above are unchanged.

The versioned `Milestone09cIntegrationOrdinary` regression imports the ordinary root.
`Milestone09cIntegrationProof` consumes the mixed theorem through the proof library.
The 256-byte dispatch regression covers 122 supported instructions, 26 assigned but unsupported instructions, 107 unassigned bytes, and INVALID.
These counts describe this restricted frame, not the full Cancun EVM.

## KECCAK256 execution (09d)

KECCAK256 pops the offset and length before checking gas.
It charges for rounded input words and memory expansion before reading memory.
An empty input does not expand memory, even at the maximum offset.
The digest is pushed as a big-endian word.
The raw sparse store is unchanged for every outcome.
`PureMemoryStep` excludes KECCAK256 because its allocation can expand.
Callers constructing that predicate must prove the additional exclusion.

The execution contracts prove the result relative to the shared `keccak256` primitive.
The independent bit-coordinate specification is `Cryptography.Hash.KeccakBits`.
`Kernel.keccak256_eq` replaces the permutation inside the same lane sponge.
It does not by itself establish agreement with the independent bit sponge.
`KeccakBits.keccak256_eq` proves that agreement for every byte input.
`Frame.independentSpongeLink_keccakBits` supplies the concrete link.
`Frame.keccak_step_actual_bits` derives the bit sponge digest from actual execution.

The bit model follows FIPS 202 section 3 and section 4, Algorithm 8.
It uses pad10*1 and Keccak[512] from sections 5.1 and 5.2.
The proof relates the permutation, padding bits, blocks, absorption and output bytes.
It applies to every byte input and every lane state used during absorption.
Packing and unpacking are inverse for arbitrary bit states and lane states.
The step and permutation correspondences therefore cover arbitrary bit states.
Iota and round correspondences use the 24 source round indices.
Known-answer regressions do not establish these universal equalities by themselves.
The pinned source review is agent inspection, not human approval or a Python-to-Lean proof.
The full Cancun EVM remains outside this proved instruction subset.

## 09e1 message environment

`CallData.Context` contains input bytes and an `Environment.Context`.
Constructors must now supply both fields.
The environment supplies the current target, transaction origin, immediate caller,
message value and effective transaction gas price.
The three addresses are `Fin (2^160)` and the two amounts are `Word` values.
The gas price boundary accepts values below `2^256`, as required by the source
conversion to U256.
It does not model the transaction envelope, calls or account balances.

ADDRESS, ORIGIN, CALLER, CALLVALUE and GASPRICE charge two gas before stack push.
They preserve the context, return data, code and memory.
`Frame.step_observation_actual` states their exact successful frame fields.
`Frame.step_observation_gas` and `Frame.step_observation_full` state the errors.
`Frame.environment_address_values` and `Frame.environment_word_values` connect
the independent observation selection to the supplied fields.
`Environment.addressWord_toNat`, `addressWord_injective`, and `addressWord_codec`
state the address conversion contracts.
`Runner.EnvironmentProgram.run` runs all five instructions over arbitrary context,
return data, residual stack, gas and valid memory.
`Runner.run_context_unchanged` covers every bounded result, including exceptions,
unsupported instructions and fuel exhaustion.

The public `Frame.observe` helper accepts any natural-valued function.
`observe_gas`, `observe_full`, `observe_success` and `observe_actual` cover its
errors and exact successful output.
`observationWord_toNat` specifies reduction modulo `2^256` for every natural input.
The five environment observations stay in range by their field types.

The 09e1 migration changes `CallData.Context` construction from `⟨data⟩` to
`⟨data, environment⟩`.
The new field is explicit and has no default.
The address fields are independent, and gas price must fit in a word.
Cancun's source stores gas price as Uint and constructs U256 at GASPRICE.
This interface covers the representable U256 inputs.

`Environment.addressWord` has numeric, injectivity and word-codec contracts in
`addressWord_toNat`, `addressWord_injective` and `addressWord_codec`.
`observationWord_toNat` covers the complete natural-input domain of
`Frame.observationWord`, including its modulo extension.
`observationWord_exact` and `observationWord_checked` cover word-sized inputs.
`observe_gas`, `observe_full`, `observe_success` and `observe_actual` cover
`Frame.observe` for arbitrary frames and value functions, without an opcode premise.
The last theorem derives the complete output fields from a successful call.

For each environment observation, `Observation.opcode` and `Observation.value`
select its byte and source field.
`environment_address_values` and `environment_word_values` connect these
selections to the supplied metadata.
The inherited `step_observation_gas`, `step_observation_full`,
`step_observation` and `step_observation_actual` apply to each selection.
`rule_total` and `step_iff_rule` cover all executable frame outcomes.
The inherited `run_context_unchanged` preserves the environment for every
bounded result.
`Runner.EnvironmentProgram.run` specifies the combined five-opcode run.

## 09e2a block environment

`Environment.Context` also requires seven block and chain fields.
Every constructor supplies them explicitly.
Coinbase uses the existing 160-bit address type.
Chain ID uses `Fin (2^64)` and is zero extended to a word.
Timestamp and PREVRANDAO are words.
Number, gas limit and base fee accept the U256-representable source values.
The Cancun source converts those three `Uint` values to U256.
The context does not represent larger source values for those conversions.
PREVRANDAO is the big-endian decoded value of the supplied 32 bytes.
`Frame.prevRandao_codec` relates accepted bytes and their word representation.

The seven instructions charge two gas before pushing the selected field.
`Frame.block_observation_values` connects each selection to its field.
`Frame.block_observation_actual` derives the stack and context from actual success.
`Runner.BlockEnvironmentProgram.run` covers arbitrary accepted context and memory.
The context supplies metadata and does not validate a block or calculate fees.
BLOCKHASH and blob queries remain outside this slice.
