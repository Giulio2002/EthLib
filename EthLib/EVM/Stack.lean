module

public import EthLib.EVM.Word

/-!
# EVM stack helpers

The ordering and limit follow execution-specs commit
`fd9298410ec7218838c8348f69c1eb633f1797dc`, Cancun `vm/stack.py`.
The list here is top-first, the reverse of the source list.
These helpers do not charge gas or execute instructions.
-/

@[expose] public section

namespace EthLib.EVM

/-- A stack with its top at the head and at most 1024 entries. -/
abbrev Stack := { entries : List Word // entries.length ≤ 1024 }

/-- Failure of a stack helper. -/
inductive StackError where
  | overflow
  | underflow
  deriving DecidableEq, Repr

/-- Failure of the checked list boundary. -/
inductive StackInputError where
  | tooManyEntries
  deriving DecidableEq, Repr

namespace Stack

/-- Observe entries in top-first order. -/
def toList (s : Stack) : List Word := s.val

/-- Number of entries. -/
def height (s : Stack) : Nat := s.val.length

/-- The empty stack. -/
def empty : Stack := ⟨[], by simp⟩

/-- Check a top-first list without changing its entries. -/
def ofList (xs : List Word) : Except StackInputError Stack :=
  if h : xs.length ≤ 1024 then .ok ⟨xs, h⟩ else .error .tooManyEntries

/-- Push at the top, as in Cancun `vm/stack.py`, `push`. -/
def push (s : Stack) (x : Word) : Except StackError Stack :=
  if h : s.val.length < 1024 then
    .ok ⟨x :: s.val, by simp only [List.length_cons]; omega⟩
  else .error .overflow

/-- Remove the top, as in Cancun `vm/stack.py`, `pop`. -/
def pop (s : Stack) : Except StackError (Word × Stack) :=
  match h : s.val with
  | [] => .error .underflow
  | x :: xs => .ok (x, ⟨xs, by have := s.property; simp only [h, List.length_cons] at this; omega⟩)

/-- Duplicate the indexed entry, where zero denotes DUP1.

The checks follow Cancun `vm/instructions/stack.py`, `dup_n`, and
`vm/stack.py`, `push`, at execution-specs commit
`fd9298410ec7218838c8348f69c1eb633f1797dc`.
-/
def dup (s : Stack) (i : Fin 16) : Except StackError Stack :=
  if h : i.val < s.val.length then
    if room : s.val.length < 1024 then
      .ok ⟨s.val[i.val] :: s.val, by simp only [List.length_cons]; omega⟩
    else .error .overflow
  else .error .underflow

/-- Exchange the top with the indexed entry, where zero denotes SWAP1.

The source is Cancun `vm/instructions/stack.py`, `swap_n`, at
execution-specs commit `fd9298410ec7218838c8348f69c1eb633f1797dc`.
-/
def swap (s : Stack) (i : Fin 16) : Except StackError Stack :=
  if h : i.val + 1 < s.val.length then
    let top := s.val[0]'(by omega)
    let other := s.val[i.val + 1]
    .ok ⟨(s.val.set 0 other).set (i.val + 1) top, by simpa using s.property⟩
  else .error .underflow

end Stack
end EthLib.EVM
