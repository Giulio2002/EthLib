import EthLib.EVM

open EthLib.EVM EthLib.EVM.World

namespace WorldOrdinary

def first : Address := ⟨1, by decide⟩
def second : Address := ⟨2, by decide⟩
def rich : Account := ⟨4, 7, emptyCodeHash⟩
def initial : State := ⟨[(first, rich), (second, emptyAccount)],
  [((first, 1), 9), ((second, 2), 11)], []⟩

def program : Except StorageError State := do
  let s ← setStorage initial first 1 0
  let s ← setStorage s first 2 5
  pure (destroyAccount s second)

example : getAccountOptional initial first = some rich := by decide
example : getAccountOptional initial second = some emptyAccount := by decide
example : getAccountOptional initial ⟨3, by decide⟩ = none := by decide
example : getStorage initial second 2 = 11 := by decide
example : (program.map fun s => (getStorage s first 1, getStorage s first 2,
    getAccountOptional s second, getStorage s second 2)) = .ok (0, 5, none, 0) := by rfl

end WorldOrdinary

namespace WorldOrdinary

def third : Address := ⟨3, by decide⟩
def codeA : ByteArray := ⟨#[1, 2]⟩
def codeB : ByteArray := ⟨#[3]⟩
def duplicateWorld : State := ⟨
  [(first, rich), (first, emptyAccount), (second, emptyAccount)],
  [((first, 1), 9), ((first, 1), 13), ((second, 2), 11)],
  [(7, codeA), (7, codeB), (emptyCodeHash, codeB)]⟩

example : getAccountOptional duplicateWorld first = some rich := by rfl
example : getStorage duplicateWorld first 1 = 9 := by rfl
example : getCode duplicateWorld 7 = some codeA := by rfl
example : getCode duplicateWorld emptyCodeHash = some ByteArray.empty := by rfl
example : getCode duplicateWorld 8 = none := by rfl
example : getAccount duplicateWorld third = emptyAccount := by rfl
example : getAccount duplicateWorld first = rich := by rfl
example : accountExists duplicateWorld second = true := by rfl
example : accountExists duplicateWorld third = false := by rfl
example : accountExistsAndIsEmpty duplicateWorld second = true := by rfl
example : accountExistsAndIsEmpty duplicateWorld third = false := by rfl
example : accountExistsAndIsEmpty duplicateWorld first = false := by rfl
example : setStorage duplicateWorld third 1 5 = .error .missingAccount := by rfl

def removed : State := setAccount duplicateWorld first none
example : getAccountOptional removed first = none := by rfl
example : getStorage removed first 1 = 9 := by rfl
example : getAccountOptional (setAccount removed first (some emptyAccount)) first =
    some emptyAccount := by rfl

def cleared : State := destroyStorage duplicateWorld first
example : getAccountOptional cleared first = some rich := by rfl
example : getStorage cleared first 1 = 0 := by rfl
example : getStorage cleared second 2 = 11 := by rfl

def cleaned : State := modifyState duplicateWorld first (fun _ => emptyAccount)
def updated : State := modifyState duplicateWorld first (fun x => { x with nonce := x.nonce + 1 })
example : getAccountOptional cleaned first = none := by rfl
example : getStorage cleaned first 1 = 0 := by rfl
example : getAccountOptional updated first = some ⟨5, 7, emptyCodeHash⟩ := by rfl
example : getStorage updated first 1 = 9 := by rfl

/-- The same write followed by destruction covered by `write_then_destroy`. -/
def writeThenDestroy : Except StorageError State := do
  let s ← setStorage duplicateWorld first 1 5
  pure (destroyAccount s first)

example : (writeThenDestroy.map fun s => (getAccountOptional s first, getStorage s first 1,
    getAccountOptional s second, getStorage s second 2, getCode s 7)) =
    .ok (none, 0, some emptyAccount, 11, some codeA) := by rfl

-- Run the public operations through the evaluator as well as kernel reduction.
#eval do
  let s := duplicateWorld
  let t ← match setStorage s first 1 5 with
    | .ok t => pure t
    | .error _ => throw (IO.userError "present storage write failed")
  let d := destroyAccount t first
  let checks := [
    getAccountOptional s first == some rich,
    getAccount s third == emptyAccount,
    getStorage s first 1 == 9,
    getCode s 7 == some codeA,
    getCode s emptyCodeHash == some ByteArray.empty,
    accountExists s second,
    !accountExists s third,
    accountExistsAndIsEmpty s second,
    !(accountExistsAndIsEmpty s third),
    getAccountOptional removed first == none,
    getStorage removed first 1 == 9,
    getStorage cleared first 1 == 0,
    getAccountOptional cleaned first == none,
    getStorage updated first 1 == 9,
    getAccountOptional d first == none,
    getStorage d second 2 == 11,
    getCode d 7 == some codeA,
    match setStorage s third 1 5 with
      | .error .missingAccount => true
      | .ok _ => false]
  unless checks.all id do
    throw (IO.userError "world operation check failed")

end WorldOrdinary
