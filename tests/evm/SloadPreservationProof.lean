import EthLib.EVM.Proofs.Runner.SelfBalance

open EthLib.EVM

namespace StorageReadPreservationConsumer

private theorem notSloadOfAt {s : Frame.State} {op : Opcode}
    (at_ : Frame.At s (some op)) (different : op ≠ .sload) :
    ¬ Frame.At s (some .sload) := by
  obtain ⟨bounds, decoded⟩ := at_
  rintro ⟨_, other⟩
  have equal : op = .sload := Option.some.inj (decoded.symm.trans other)
  exact different equal

-- Both account-reading opcodes remain within the preservation scope.
theorem balance_step (s : Frame.State) (at_ : Frame.At s (some .balance)) :
    (Frame.step s).frame.tracker.storageReads = s.tracker.storageReads :=
  Frame.step_storageReads_unchanged_of_not_sload s (notSloadOfAt at_ (by decide))

theorem selfbalance_step (s : Frame.State) (at_ : Frame.At s (some .selfbalance)) :
    (Frame.step s).frame.tracker.storageReads = s.tracker.storageReads :=
  Frame.step_storageReads_unchanged_of_not_sload s (notSloadOfAt at_ (by decide))

-- The predicate accepts an actual BALANCE, SELFBALANCE, STOP trace.
theorem mixed_trace (s t u v : Frame.State)
    (balanceAt : Frame.At s (some .balance)) (balanceStep : Frame.step s = .continue t)
    (selfAt : Frame.At t (some .selfbalance)) (selfStep : Frame.step t = .continue u)
    (stopAt : Frame.At u (some .stop)) (stopStep : Frame.step u = .stop v) :
    (Runner.run 3 s).frame.tracker.storageReads = s.tracker.storageReads := by
  have trace : Runner.NoSloadRun 3 s := by
    simp only [Runner.NoSloadRun, balanceStep, selfStep, stopStep]
    exact ⟨notSloadOfAt balanceAt (by decide), notSloadOfAt selfAt (by decide),
      notSloadOfAt stopAt (by decide), trivial⟩
  exact Runner.run_storageReads_unchanged_of_no_sload 3 s trace

theorem exhausted_result (fuel : Nat) (s t : Frame.State) (trace : Runner.NoSloadRun fuel s)
    (run : Runner.run fuel s = .exhausted t) : t.tracker.storageReads = s.tracker.storageReads := by
  have result := Runner.run_storageReads_unchanged_of_no_sload fuel s trace
  simpa [run, Runner.Result.frame] using result

theorem stopped_result (fuel : Nat) (s t : Frame.State) (trace : Runner.NoSloadRun fuel s)
    (run : Runner.run fuel s = .stopped t) : t.tracker.storageReads = s.tracker.storageReads := by
  have result := Runner.run_storageReads_unchanged_of_no_sload fuel s trace
  simpa [run, Runner.Result.frame] using result

theorem exception_result (fuel : Nat) (s t : Frame.State) (reason : Frame.Exception) (trace : Runner.NoSloadRun fuel s)
    (run : Runner.run fuel s = .exception t reason) : t.tracker.storageReads = s.tracker.storageReads := by
  have result := Runner.run_storageReads_unchanged_of_no_sload fuel s trace
  simpa [run, Runner.Result.frame] using result

theorem unsupported_result (fuel : Nat) (s t : Frame.State) (op : Opcode) (trace : Runner.NoSloadRun fuel s)
    (run : Runner.run fuel s = .unsupported t op) : t.tracker.storageReads = s.tracker.storageReads := by
  have result := Runner.run_storageReads_unchanged_of_no_sload fuel s trace
  simpa [run, Runner.Result.frame] using result

theorem unreachable_revert (fuel : Nat) (s t : Frame.State) (gas : Nat) (output : ByteArray) :
    Runner.run fuel s ≠ .reverted t gas output := Runner.run_not_reverted fuel s t gas output

#print axioms balance_step
#print axioms selfbalance_step
#print axioms mixed_trace
#print axioms exhausted_result
#print axioms stopped_result
#print axioms exception_result
#print axioms unsupported_result
#print axioms unreachable_revert

end StorageReadPreservationConsumer
