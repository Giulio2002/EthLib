# Amsterdam blob fee migration, version 23a

The execution-specs revision is `fd9298410ec7218838c8348f69c1eb633f1797dc`.
The EIPs revision is `dc5d5fa688b7fe87b95a907fcc128b4fde2f4d2f`.
The following SHA-256 hashes identify the retrieved source bytes.
The Amsterdam, numeric and mainnet asset blobs matched the pinned Git tree.

```text
src/ethereum/forks/cancun/vm/gas.py  404361c06b0936e9d3155bb941a21d19128eed51b115e07cdf632557794aad70
src/ethereum/forks/prague/vm/gas.py  5e68950e3135abf34a32b0b5ad7f14143162638b51e9b27fdabc5005f1f39cb0
src/ethereum/forks/osaka/vm/gas.py  9ecbaf8bdb88c7d8178e4669b86c0e026fe63bcbf93cbb43f5c636b74e2b27de
src/ethereum/forks/bpo1/vm/gas.py  47f3707979921e29b01a22f7186b22d4eb6b016ecc92ddeacc1abaff729afc98
src/ethereum/forks/bpo2/vm/gas.py  ca6d26211fe32a4cd95c0c20f8110d34c5acef4a8d87023ec197ebc0505f1ebb
src/ethereum/forks/amsterdam/vm/gas.py  67973191c49234387186ad17316c556adab73723f782e95104dd3a949132367c
src/ethereum/forks/amsterdam/vm/instructions/environment.py  8c57bd699b99ff8b4d8e41e6a9c89cd1a03dda8160bf1d6dffe091932ec03657
src/ethereum/forks/amsterdam/vm/__init__.py  72bc02de1fc03a5a7ec70725cc8b8dd18241eb1a4b6e598f059505399cbefdab
src/ethereum/utils/numeric.py  cb1db3b70f2e4b2998c3e05d3dc0e308a8414f1794c0f54fa31c4698a80fdfd5
src/ethereum/assets/mainnet.json  48bb73806f4ed8f0e4f869cb0bc7ba2e1e5724ceb08c9ec079170dfd63042d65
EIPS/eip-4844.md  2772bdb675d90d89ebb4bf74269e48c8ea46745e78161c8574ffa78328b31885
EIPS/eip-7691.md  12205332a3d2e78a6e3847028cd613c7a2e448c6bdee258e46794838ff537c83
EIPS/eip-7840.md  151ed7c2261c71c9e987ef1967ccf58ffc3cbc0f735bc69f60efca2aae35b6e8
EIPS/eip-7892.md  883aa3c8d81c67591f7806ac9b18b84887ebf2eafb2379a6925932e3d62dec76
EIPS/eip-7918.md  a6aa9e0972cf2f629b5d47d3cf9bdeca416e30c58479c21651d02518ea7522e4
EIPS/eip-8134.md  4fda2996504a9b519ecd8776cfb27f4690f5d015daac266a3adceac1dfc1552d
EIPS/eip-8135.md  82defd661ed11920499d23304fb7c9c23f48a8fdeb6af61db5d3da98f4251bb0
```

Amsterdam `gas.py` gives the minimum price 1 and update fraction 11684671.
Its `calculate_blob_gas_price` passes these and U64 excess to `taylor_exponential`.
`environment.py` charges two gas and passes block excess to that function.
It converts the result to U256 before pushing it.
`numeric.py` defines the integer recurrence and its truncated divisions.

EIP-4844 specifies the Cancun fraction 3338477.
EIP-7691 changes the fraction at Prague to 5007716.
EIP-7840 puts per-fork blob parameters in client configuration.
EIP-7892 specifies selecting the current block's blob schedule.
EIP-8134 and EIP-8135 specify the BPO1 and BPO2 fractions.
EIP-7918 changes the excess gas transition and uses the current schedule.
The pinned mainnet genesis asset does not supply the Amsterdam schedule.

`BlobFee.calculateBlobGasPrice` remains the Cancun calculation.
`BlobFee.calculateWith` takes an explicit positive update fraction and U64 excess.
`BlobFee.cancun`, `prague`, `osaka`, `bpo1`, `bpo2` and `amsterdam` name snapshot fractions.
`Environment.Context.blobFeeSchedule` supplies the current block configuration.
Structure literals default to Cancun, while positional constructors require the new final field.
Frame observation and runner contracts now quantify over this field.
The caller selects the schedule and must supply the applicable network configuration.

The recurrence relation proves the arithmetic for every positive denominator.
The executable excess domain is U64, as in the source.
A fee below `2^256` agrees with checked conversion.
The frame's modulo result above that boundary is a total extension.
The mathematical termination proof does not give a practical full-U64 runtime bound.
This slice does not implement the excess gas transition, reserve price, block validity, other Amsterdam opcode or gas changes, or fixtures.
It does not establish Python equivalence or human approval.
