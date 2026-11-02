module

public import EthLib.EVM.Word

/-!
# Cancun blob fee arithmetic

Cancun execution-specs revision `fd9298410ec7218838c8348f69c1eb633f1797dc`,
`ethereum/utils/numeric.py`, `taylor_exponential`, defines the integer recurrence.
`vm/gas.py`, `calculate_blob_gas_price`, supplies the constants.
The divisions truncate at every iteration.
-/

@[expose] public section
namespace EthLib.EVM.BlobFee

/-- Sum the integer recurrence until its accumulated term is zero. -/
def recurrence (numerator denominator index term output : Nat)
    (denominatorPositive : 0 < denominator) (indexPositive : 0 < index) : Nat :=
  if term = 0 then output else
    recurrence numerator denominator (index + 1)
      (term * numerator / (denominator * index)) (output + term)
      denominatorPositive (by omega)
termination_by (numerator + 1 - index, term)
decreasing_by
  simp_wf
  by_cases h : index ≤ numerator
  · left
    omega
  · have same : numerator - index = numerator + 1 - index := by omega
    rw [same]
    right
    -- Once the index exceeds the numerator, each positive term decreases.
    have denominatorLarger : numerator < denominator * index :=
      Nat.lt_of_lt_of_le (Nat.lt_of_not_ge h) (Nat.le_mul_of_pos_left index denominatorPositive)
    have termPositive : 0 < term := by omega
    exact (Nat.div_lt_iff_lt_mul (Nat.mul_pos denominatorPositive indexPositive)).2
      (Nat.mul_lt_mul_of_pos_left denominatorLarger termPositive)

/-- The source integer approximation with a positive denominator. -/
def taylorExponential (factor numerator : Nat) (denominator : {d : Nat // 0 < d}) : Nat :=
  recurrence numerator denominator.val 1 (factor * denominator.val) 0 denominator.property (by omega) /
    denominator.val

/-- Cancun `gas.py` uses a minimum blob gas price of one. -/
def minBlobGasPrice : Nat := 1

/-- Cancun `gas.py` uses this update fraction for blob gas prices. -/
def blobBaseFeeUpdateFraction : {d : Nat // 0 < d} := ⟨3338477, by decide⟩

/-- Cancun `calculate_blob_gas_price`, before the source U256 conversion. -/
def calculateBlobGasPrice (excessBlobGas : Fin (2 ^ 64)) : Nat :=
  taylorExponential minBlobGasPrice excessBlobGas.val blobBaseFeeUpdateFraction

end EthLib.EVM.BlobFee
