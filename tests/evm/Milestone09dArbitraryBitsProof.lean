import EthLib.Cryptography.Proofs.Hash.KeccakBitsRepresentation

open EthLib.Cryptography.Hash

example (a : KeccakBits.State) : KeccakBits.ofLanes (KeccakBits.toLanes a) = a :=
  KeccakBits.ofLanes_toLanes a

example (a : Keccak.State) : KeccakBits.toLanes (KeccakBits.ofLanes a) = a :=
  KeccakBits.toLanes_ofLanes a

example (a : KeccakBits.State) :
    KeccakBits.toLanes (KeccakBits.theta a) = Keccak.theta (KeccakBits.toLanes a) :=
  KeccakBits.toLanes_theta a

example (a : KeccakBits.State) :
    KeccakBits.toLanes (KeccakBits.rho a) = Keccak.rho (KeccakBits.toLanes a) :=
  KeccakBits.toLanes_rho a

example (a : KeccakBits.State) :
    KeccakBits.toLanes (KeccakBits.pi a) = Keccak.pi (KeccakBits.toLanes a) :=
  KeccakBits.toLanes_pi a

example (a : KeccakBits.State) :
    KeccakBits.toLanes (KeccakBits.chi a) = Keccak.chi (KeccakBits.toLanes a) :=
  KeccakBits.toLanes_chi a

example (a : KeccakBits.State) (ir : Fin 24) :
    KeccakBits.toLanes (KeccakBits.iota ir.val a) = Keccak.iota ir (KeccakBits.toLanes a) :=
  KeccakBits.toLanes_iota a ir

example (a : KeccakBits.State) (ir : Fin 24) :
    KeccakBits.toLanes (KeccakBits.round ir.val a) = Keccak.round ir (KeccakBits.toLanes a) :=
  KeccakBits.toLanes_round a ir

example (a : KeccakBits.State) :
    KeccakBits.toLanes (KeccakBits.permutation a) = Keccak.keccakF (KeccakBits.toLanes a) :=
  KeccakBits.toLanes_permutation a
