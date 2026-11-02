# Amsterdam SLOTNUM

The execution-specs revision is `fd9298410ec7218838c8348f69c1eb633f1797dc`.
Amsterdam `blocks.py`, `Header.slot_number`, and `vm/__init__.py`, `BlockEnvironment.slot_number`, use U64.
`fork.py`, `state_transition`, copies the header field into the block environment.
The context takes that value as supplied metadata.
It does not validate the header, block, or consensus slot.

Amsterdam `vm/instructions/__init__.py`, `Ops.SLOTNUM`, assigns byte `0x4b`.
`vm/instructions/block.py`, `slot_number`, charges gas, pushes the U256 conversion, and advances the program counter.
`vm/gas.py`, `GasCosts.OPCODE_SLOTNUM`, assigns two gas.
`vm/stack.py`, `push`, rejects a full stack after that charge.
EIP-7843 Specification says the consensus layer supplies the slot through the engine API.
The field is not derived from the timestamp.

The target decoder extends the Cancun subset with Osaka CLZ and Amsterdam SLOTNUM.
It does not include Amsterdam SWAPN, DUPN, or EXCHANGE.
The Cancun and Cancun-plus-CLZ classifiers exclude SLOTNUM.
This subset does not implement the complete Amsterdam transition.

`Environment.Context` requires a `slotNumber : Fin (2 ^ 64)` field.
A positional constructor supplies it immediately after `number`.
Callers must supply the block's slot metadata when constructing a context.
The value is independent of the block number and timestamp.
