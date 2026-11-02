import EthLib.EVM.Stack

open EthLib.EVM

private def same (a b : Except StackError (List Word)) : Bool :=
  match a, b with
  | .ok x, .ok y => x == y
  | .error x, .error y => decide (x = y)
  | _, _ => false

private def checkCase (n : Nat) (i : Fin 16) : Bool := Id.run do
  let xs := (List.range n).map (fun x => BitVec.ofNat 256 x)
  let .ok s := Stack.ofList xs | return false
  let dupExpected := match xs[i.val]? with
    | none => Except.error StackError.underflow
    | some x => if n = 1024 then .error .overflow else .ok (x :: xs)
  let swapExpected := match xs[0]?, xs[i.val + 1]? with
    | some top, some other =>
      .ok (other :: (xs.drop 1).take i.val ++ [top] ++ xs.drop (i.val + 2))
    | _, _ => .error StackError.underflow
  return same ((s.dup i).map Stack.toList) dupExpected &&
    same ((s.swap i).map Stack.toList) swapExpected

#eval do
  for n in [0, 1, 16, 17, 1023, 1024] do
    for i in List.finRange 16 do
      unless checkCase n i do
        throw <| IO.userError s!"stack indexed regression failed: height {n}, index {i}"
  IO.println "stack indexed: 96 cases passed"
