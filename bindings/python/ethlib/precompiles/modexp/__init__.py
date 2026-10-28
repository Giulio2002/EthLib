"""The MODEXP precompile at address `0x05`, as of the BPO2 fork.

- A length above the bound raises ValueError.
- A call with too little gas raises ValueError.
"""

# Every domain links into one extension module.
# That module lives in the `cryptography` package.
from ...cryptography import _native

MODEXP_LENGTH_HEADER_BYTES = _native.MODEXP_LENGTH_HEADER_BYTES
MODEXP_MAX_LENGTH_BYTES = _native.MODEXP_MAX_LENGTH_BYTES


def modexp(data: bytes, gas: int) -> bytes:
    """The output of the precompile on the call data, with the gas given.

    Raises ValueError when a length exceeds the bound.

    Raises ValueError when the gas is below the price.
    """
    return _native.modexp(data, gas)


def gas_cost(data: bytes) -> int:
    """The gas the precompile charges for the call data.

    Raises ValueError when a length exceeds the bound.
    """
    return _native.modexp_gas_cost(data)


__all__ = [
    "modexp",
    "gas_cost",
    "MODEXP_LENGTH_HEADER_BYTES",
    "MODEXP_MAX_LENGTH_BYTES",
]
