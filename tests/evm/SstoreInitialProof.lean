import EthLib.EVM.Proofs.Frame.SstoreInitial

open EthLib.EVM

namespace SstoreInitialConsumer

theorem static (s : Frame.State) (h : s.isStatic = true) :
    Frame.sstore s = .exception s .writeInStaticContext := Frame.sstore_static s h

theorem dispatchStatic (s : Frame.State) (h : s.isStatic = true)
    (bounds : s.pc < s.code.size) (op : Opcode.decode s.code[s.pc] = some .sstore) :
    Frame.step s = .exception s .writeInStaticContext := Frame.step_sstore_static s h bounds op

theorem underflow (s : Frame.State) (h : s.isStatic = false) (empty : s.stack.val = []) :
    Frame.sstore s = .exception s .stackUnderflow := Frame.sstore_underflow s h empty

theorem sentry (s : Frame.State) (first rest : Stack) (key value : Word)
    (static : s.isStatic = false) (items : s.stack.val = key :: first.val)
    (items' : first.val = value :: rest.val) (gas : s.gas < 2301) :
    Frame.sstore s = .exception { s with stack := rest } .outOfGas :=
  Frame.sstore_sentry s first rest key value static items items' gas

#print axioms static
#print axioms dispatchStatic
#print axioms underflow
#print axioms sentry
end SstoreInitialConsumer
