"""XMSS signatures: key generation, signing and verification only.

- Malformed arguments raise TypeError, ValueError or OverflowError.
- Inputs the spec rejects raise RuntimeError.
"""

from .._native import (
    xmss_key_gen,
    xmss_sign,
    xmss_verify,
    XMSS_MESSAGE_LEN as MESSAGE_LEN,
    XMSS_PUB_KEY_SIZE as PUB_KEY_SIZE,
    XMSS_SEED_LEN as SEED_LEN,
    XMSS_SIG_SIZE as SIG_SIZE,
)


def key_gen(seed: bytes, epoch_start: int, epoch_end: int) -> bytes:
    """The public key grown from a seed, for epochs start to end inclusive."""
    return xmss_key_gen(seed, epoch_start, epoch_end)


def sign(seed: bytes, epoch_start: int, epoch_end: int, epoch: int, message: bytes) -> bytes:
    """Sign a message at an epoch with the key grown from a seed and epoch range."""
    return xmss_sign(seed, epoch_start, epoch_end, epoch, message)


def verify(public_key: bytes, epoch: int, message: bytes, signature: bytes) -> bool:
    """Whether a signature signs a message at an epoch under a public key."""
    return xmss_verify(public_key, epoch, message, signature)


__all__ = [
    "key_gen",
    "sign",
    "verify",
    "MESSAGE_LEN",
    "PUB_KEY_SIZE",
    "SEED_LEN",
    "SIG_SIZE",
]
