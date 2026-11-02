module

public import EthLib.EVM.ReturnData

@[expose] public section
namespace EthLib.EVM.ReturnData

/-- Every accepted range satisfies the source bound. -/
theorem read_ok_bound (data : ByteArray) (offset length : Nat) (bytes : List UInt8)
    (h : read data offset length = .ok bytes) : offset + length ≤ data.size := by
  unfold read at h
  split at h
  next bound => exact bound
  next => contradiction

/-- Every rejected range exceeds the source bound. -/
theorem read_error_bound (data : ByteArray) (offset length : Nat)
    (h : read data offset length = .error .outOfBounds) : data.size < offset + length := by
  unfold read at h
  split at h
  next => contradiction
  next bound => exact Nat.lt_of_not_ge bound

/-- An accepted read is the exact slice of the source. -/
theorem read_ok_bytes (data : ByteArray) (offset length : Nat) (bytes : List UInt8)
    (h : read data offset length = .ok bytes) :
    bytes = (data.data.toList.drop offset).take length := by
  unfold read at h
  split at h
  next => exact (Except.ok.inj h).symm
  next => contradiction

/-- A source range is accepted exactly when it is within the buffer. -/
theorem read_success_iff (data : ByteArray) (offset length : Nat) :
    (∃ bytes, read data offset length = .ok bytes) ↔ offset + length ≤ data.size := by
  by_cases bound : offset + length ≤ data.size <;> simp [read, bound]

/-- A source range is rejected exactly when its end exceeds the buffer. -/
theorem read_error_iff (data : ByteArray) (offset length : Nat) :
    read data offset length = .error .outOfBounds ↔ data.size < offset + length := by
  simp [read, Nat.not_le]

/-- A successful read has the requested length. -/
theorem read_ok_length (data : ByteArray) (offset length : Nat) (bytes : List UInt8)
    (h : read data offset length = .ok bytes) : bytes.length = length := by
  have bound := read_ok_bound data offset length bytes h
  rw [read_ok_bytes data offset length bytes h]
  simp only [List.length_take, List.length_drop, Array.length_toList]
  have size : data.data.size = data.size := rfl
  rw [size]
  omega

/-- Each byte of a successful read is the byte at the corresponding source index. -/
theorem read_ok_index (data : ByteArray) (offset length : Nat) (bytes : List UInt8)
    (h : read data offset length = .ok bytes) (i : Nat) (hi : i < length) :
    bytes[i]'(by rw [read_ok_length data offset length bytes h]; exact hi) =
      data[offset + i]'(by have b := read_ok_bound data offset length bytes h; omega) := by
  have eq := read_ok_bytes data offset length bytes h
  subst bytes
  simp only [List.getElem_take, List.getElem_drop, Array.getElem_toList]
  rfl

end EthLib.EVM.ReturnData
