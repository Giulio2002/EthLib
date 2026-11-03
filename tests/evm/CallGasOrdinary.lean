import EthLib.EVM

open EthLib.EVM

private def check (ok : Bool) : IO Unit :=
  if ok then pure () else throw (IO.userError "call gas mismatch")

-- 6400 available gives a 6300 cap; the extra cost is charged separately.
#eval check (decide (Gas.Call.calculate 0 7000 6600 100 100 2300 = ⟨6400, 6300⟩))
-- A value stipend is added to the child grant, not the parent charge.
#eval check (decide (Gas.Call.calculate 1 7000 6600 100 100 2300 = ⟨6400, 8600⟩))
-- The source returns an uncapped result before the later failed charge.
#eval check (decide (Gas.Call.calculate 1 7000 199 100 100 2300 = ⟨7100, 9300⟩))
-- At the exact affordability boundary, no execution gas can be forwarded.
#eval check (decide (Gas.Call.calculate 1 7000 200 100 100 2300 = ⟨100, 2300⟩))
