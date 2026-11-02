import EthLib.EVM.Frame

open EthLib.EVM

-- The helper operates on its frame even when code and PC cannot dispatch it.
/-- info: (true, true, true, true) -/
#guard_msgs in
#eval let s : Frame.State := ⟨⟨#[0xfe]⟩, 99, ⟨[1, 1, 2], by decide⟩, 9,
    Memory.Allocation.empty, by intro a _h; rfl, ⟨⟨#[99]⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, []⟩⟩, ⟨#[1, 2, 3]⟩⟩
  match Frame.returnDataCopy s with
  | .continue t => (t.pc == 100, t.gas == 0,
      Memory.readRange t.memory.store 0 4 == [0, 2, 3, 0], t.returnData == s.returnData)
  | _ => (false, false, false, false)
