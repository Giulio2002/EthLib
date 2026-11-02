import EthLib.EVM.Runner

open EthLib.EVM

private def state : Frame.State :=
  ⟨⟨#[0x20]⟩, 0, ⟨[0, 0], by decide⟩, 30, Memory.Allocation.empty,
    by intro a _; rfl, ⟨ByteArray.empty, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, []⟩⟩, ByteArray.empty⟩

-- Empty Keccak-256, Keccak team's ShortMsgKAT_256.txt, Len = 0.
/-- info: true -/
#guard_msgs in
#eval match Runner.run 1 state with
  | .exhausted s => s.stack.val.head!.toNat ==
      89477152217924674838424037953991966239322087453347756267410168184682657981552
  | _ => false

-- The public helper ignores unrelated code and an out-of-bounds program counter.
private def helperState : Frame.State :=
  { state with code := ⟨#[0xfe]⟩, pc := 99 }

/-- info: (true, 100, 0) -/
#guard_msgs in
#eval match Frame.keccak helperState with
  | .continue s => (s.stack.val.head!.toNat ==
      89477152217924674838424037953991966239322087453347756267410168184682657981552,
      s.pc, s.gas)
  | _ => (false, 0, 1)
