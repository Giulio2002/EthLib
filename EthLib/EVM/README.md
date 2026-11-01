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

# Byte contents contract

The sparse store models byte contents independently of allocated memory size.
The source is Cancun execution-specs revision `fd9298410ec7218838c8348f69c1eb633f1797dc`, `vm/memory.py`, functions `memory_write` and `memory_read_bytes`.
Those functions access an allocated bytearray.
Interpreting unallocated addresses as zero in a total function is this module's abstraction, not a claim that the source reads outside the bytearray.
Allocation, expansion, gas, ranges and instructions remain outside this contract.

Every finite list of address and byte pairs is a valid store.
The first occurrence of an address determines its byte, and an absent address reads zero.
A write adds one pair, including for zero, so it does not allocate up to the address.
The finite support list contains every address whose observed byte is nonzero, but may also contain zero and shadowed writes.
It is not the logical memory size.

The kernel checks that empty reads zero, a write changes exactly its address, and support remains finite.
It checks overwrite, write-back and commutation for distinct addresses as equality of total observed byte functions.
These equalities do not assert equality of write histories.
The source interpretation is a human reading; the proofs establish refinement to the stated Lean abstraction.
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
