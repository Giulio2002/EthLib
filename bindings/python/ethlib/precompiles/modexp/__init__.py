# The Lean objects of every domain link into one extension module, which
# lives in the `cryptography` package.
from ...cryptography import _native

MODEXP_LENGTH_HEADER_BYTES = _native.MODEXP_LENGTH_HEADER_BYTES
MODEXP_MAX_LENGTH_BYTES = _native.MODEXP_MAX_LENGTH_BYTES


def modexp(data: bytes, gas: int) -> bytes:
    """Run the MODEXP precompile on `data` with `gas` available.

    Raises `ValueError` when a length exceeds `MODEXP_MAX_LENGTH_BYTES`
    or when `gas` is below the price.
    """
    return _native.modexp(data, gas)


def gas_cost(data: bytes) -> int:
    """The gas the precompile charges for `data`.

    Raises `ValueError` when a length exceeds `MODEXP_MAX_LENGTH_BYTES`.
    """
    return int.from_bytes(_native.modexp_gas_cost(data), "big")


__all__ = [
    "modexp",
    "gas_cost",
    "MODEXP_LENGTH_HEADER_BYTES",
    "MODEXP_MAX_LENGTH_BYTES",
]
