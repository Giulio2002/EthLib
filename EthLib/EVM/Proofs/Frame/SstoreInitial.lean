module

public import EthLib.EVM.Frame
public import EthLib.EVM.Proofs.Stack

/-! Initial source-order facts for Amsterdam `storage.py`, `sstore`. -/

@[expose] public section
namespace EthLib.EVM.Frame

/-- A static frame fails before inspecting its stack or gas. -/
theorem sstore_static (s : State) (static : s.isStatic = true) :
    sstore s = .exception s .writeInStaticContext := by
  simp [sstore, static]

/-- The actual dispatcher reaches the same static failure. -/
theorem step_sstore_static (s : State) (static : s.isStatic = true)
    (inBounds : s.pc < s.code.size) (opcode : Opcode.decode s.code[s.pc] = some .sstore) :
    step s = .exception s .writeInStaticContext := by
  simp [step, inBounds, opcode, sstore, static]

/-- An empty non-static stack fails before the gas guard. -/
theorem sstore_underflow (s : State) (static : s.isStatic = false)
    (empty : s.stack.val = []) : sstore s = .exception s .stackUnderflow := by
  have pop : s.stack.pop = .error .underflow := (Proofs.Stack.pop_underflow_iff _).mpr empty
  simp [sstore, static, pop, failStack]

/-- The stipend sentry runs after both pops and before warming or state access. -/
theorem sstore_sentry (s : State) (first rest : Stack) (key value : Word)
    (static : s.isStatic = false) (items : s.stack.val = key :: first.val)
    (items' : first.val = value :: rest.val) (gas : s.gas < 2301) :
    sstore s = .exception { s with stack := rest } .outOfGas := by
  have pop : s.stack.pop = .ok (key, first) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  have pop' : first.pop = .ok (value, rest) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items'
  by_cases warm : (s.context.environment.currentTarget, key) ∈ s.warmSlots <;>
    simp [sstore, static, pop, pop', warm, gas]

end EthLib.EVM.Frame
