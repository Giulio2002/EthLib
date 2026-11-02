# Amsterdam immediate stack instructions

The source is execution-specs revision `fd9298410ec7218838c8348f69c1eb633f1797dc`.
Amsterdam `vm/instructions/stack.py` defines DUPN, SWAPN and EXCHANGE.
`vm/stack.py`, `decode_single` and `decode_pair`, define the valid immediate bytes and indices.
EIP-8024 Specification describes the same instruction encoding.

The current `Opcode.decode` assigns `0xe6`, `0xe7` and `0xe8`.
Consumers matching every `Opcode` must handle the three new constructors.
`decodeCancun` and `decodeCancunClz` exclude them.
`decodeCancunClzSlotnum` retains the preceding decoder with CLZ and SLOTNUM.

The frame charges three gas before reading and validating the immediate.
An invalid immediate produces `Frame.Exception.invalidParameter`.
A missing byte reads as zero.
Stack underflow and overflow follow the charge and immediate checks.
A successful instruction advances the program counter by two.
Natural program counters and arbitrary direct helper inputs extend the source's bounded execution domain.

Amsterdam `vm/runtime.py`, `get_valid_jump_destinations`, skips only PUSH data.
It does not skip the bytes after these instructions.
The scanner API and its boundary rule are unchanged.
For `e6 5b`, byte 1 remains a jump destination and the immediate is invalid.
For `e6 60 5b`, the PUSH1 at byte 1 masks byte 2.

`Stack.dupAt` and `Stack.exchangeAt` use zero-based positions in a top-first list.
Their result type preserves the 1024-entry stack bound.
The frame converts the decoded source indices before using these operations.
This subset does not implement the complete Amsterdam transition.
