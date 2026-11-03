import EthLib.EVM.Proofs

open EthLib.EVM EthLib.EVM.World

namespace WorldProof

example (s : State) (a b : Address) (x : Option Account) :
    getAccountOptional (setAccount s a x) b =
      if b = a then x else getAccountOptional s b := (setAccount_spec s a x).1 b

example (s t : State) (a b : Address) (k j v : Word)
    (h : setStorage s a k v = .ok t) :
    getStorage t b j = if b = a ∧ j = k then v else getStorage s b j :=
  (setStorage_spec s t a k v h).2.1 b j

example (s : State) (a : Address) (k v : Word) :
    setStorage s a k v = .error .missingAccount ↔ getAccountOptional s a = none :=
  setStorage_error_iff s a k v

example (s : State) (a : Address) (k v : Word)
    (h : ∃ x, getAccountOptional s a = some x) : ∃ t, setStorage s a k v = .ok t :=
  (setStorage_success_iff s a k v).2 h

example (s t : State) (a : Address) (k v : Word)
    (h : setStorage s a k v = .ok t) :
    getAccountOptional (destroyAccount t a) a = none ∧
      ∀ j, getStorage (destroyAccount t a) a j = 0 :=
  ⟨(write_then_destroy s t a k v h).1, (write_then_destroy s t a k v h).2.1⟩

example (s : State) (a : Address) (f : Account → Account) :
    getAccountOptional (modifyState s a f) a =
      if f (getAccount s a) = emptyAccount then none else some (f (getAccount s a)) := by
  simpa using (modifyState_spec s a f).1 a

example (s : State) (a : Address) :
    accountExists s a = true ↔ ∃ x, getAccountOptional s a = some x := accountExists_iff s a

example (s : State) (a : Address) :
    accountExistsAndIsEmpty s a = true ↔ getAccountOptional s a = some emptyAccount :=
  accountExistsAndIsEmpty_iff s a

example (s : State) (a b : Address) (k : Word) :
    getStorage (destroyStorage s a) b k = if b = a then 0 else getStorage s b k :=
  (destroyStorage_spec s a).2.1 b k

example (s : State) (a : Address) (x y : Option Account) :
    ObservationallyEqual (setAccount (setAccount s a x) a y) (setAccount s a y) :=
  setAccount_overwrite s a x y

example (s : State) (a b : Address) (x y : Option Account) (h : a ≠ b) :
    ObservationallyEqual (setAccount (setAccount s a x) b y)
      (setAccount (setAccount s b y) a x) := setAccount_commute s a b x y h

example (s : State) (a : Address) (k v : Word)
    (h : ∃ x, getAccountOptional s a = some x) :
    ∃ t, setStorage s a k v = .ok t ∧ StorageUpdateSpec s t a k v :=
  setStorage_realizes s a k v h

example (s t u w : State) (a : Address) (k x y : Word)
    (h₁ : setStorage s a k x = .ok t) (h₂ : setStorage t a k y = .ok u)
    (h₃ : setStorage s a k y = .ok w) : ObservationallyEqual u w :=
  setStorage_overwrite s t u w a k x y h₁ h₂ h₃

example (s t u v w : State) (a b : Address) (k j x y : Word)
    (h : (a, k) ≠ (b, j)) (h₁ : setStorage s a k x = .ok t)
    (h₂ : setStorage t b j y = .ok u) (h₃ : setStorage s b j y = .ok v)
    (h₄ : setStorage v a k x = .ok w) : ObservationallyEqual u w :=
  setStorage_commute s t u v w a b k j x y h h₁ h₂ h₃ h₄

example (s : State) : getCode s emptyCodeHash = some ByteArray.empty := getCode_empty s
example (s : State) (h : Word) (ne : h ≠ emptyCodeHash) :
    getCode s h = s.codes.lookup h := getCode_nonempty s h ne

example (s : State) (a : Address) :
    getAccountOptional s a = none ↔ ∀ p ∈ s.accounts, a ≠ p.1 :=
  getAccountOptional_none_iff s a

example (s : State) (a : Address) (x : Account) :
    getAccountOptional s a = some x ↔
      ∃ before after, s.accounts = before ++ (a, x) :: after ∧
        ∀ p ∈ before, a ≠ p.1 := getAccountOptional_some_iff s a x

example (s : State) (a : Address) (k v : Word) :
    getStorage s a k = v ↔
      (v = 0 ∧ ∀ p ∈ s.storage, (a, k) ≠ p.1) ∨
      (∃ before after, s.storage = before ++ ((a, k), v) :: after ∧
        ∀ p ∈ before, (a, k) ≠ p.1) := getStorage_spec s a k v

example (s : State) (a : Address) (h : getAccountOptional s a = none) :
    getAccount s a = emptyAccount := (getAccount_spec s a).1 h

example (s : State) (a : Address) (x : Account) (h : getAccountOptional s a = some x) :
    getAccount s a = x := (getAccount_spec s a).2 x h

example (s t : State) (a : Address) (k : Word)
    (h : setStorage s a k 0 = .ok t) :
    ∀ p ∈ t.storage, p.1 ≠ (a, k) := setStorage_zero_removes s t a k h

-- Each component is used by a downstream consumer over arbitrary states.
example (s : State) (a b : Address) (x : Option Account) (k : Word) (h : b ≠ a) :
    getAccountOptional (setAccount s a x) b = getAccountOptional s b ∧
    getStorage (setAccount s a x) b k = getStorage s b k ∧
    (setAccount s a x).codes = s.codes := by
  have spec := setAccount_spec s a x
  exact ⟨by simpa [h] using spec.1 b, spec.2.1 b k, spec.2.2⟩

example (s t : State) (a b : Address) (k j v : Word) (h : b ≠ a)
    (success : setStorage s a k v = .ok t) :
    getAccountOptional t b = getAccountOptional s b ∧
    getStorage t b j = getStorage s b j ∧ t.codes = s.codes := by
  have spec := setStorage_spec s t a k v success
  exact ⟨spec.1 b, by simpa [h] using spec.2.1 b j, spec.2.2⟩

example (s t : State) (a : Address) (k v : Word)
    (success : setStorage s a k v = .ok t) :
    ∃ x, getAccountOptional s a = some x :=
  (setStorage_success_iff s a k v).1 ⟨t, success⟩

example (s : State) (a b : Address) (k : Word) (h : b ≠ a) :
    getAccountOptional (destroyStorage s a) b = getAccountOptional s b ∧
    getStorage (destroyStorage s a) b k = getStorage s b k ∧
    (destroyStorage s a).codes = s.codes := by
  have spec := destroyStorage_spec s a
  exact ⟨spec.1 b, by simpa [h] using spec.2.1 b k, spec.2.2⟩

example (s : State) (a b : Address) (k : Word) (h : b ≠ a) :
    getAccountOptional (destroyAccount s a) a = none ∧
    getStorage (destroyAccount s a) a k = 0 ∧
    getAccountOptional (destroyAccount s a) b = getAccountOptional s b ∧
    getStorage (destroyAccount s a) b k = getStorage s b k ∧
    (destroyAccount s a).codes = s.codes := by
  have spec := destroyAccount_spec s a
  exact ⟨by simpa using spec.1 a, by simpa using spec.2.1 a k,
    by simpa [h] using spec.1 b, by simpa [h] using spec.2.1 b k, spec.2.2⟩

example (s : State) (a b : Address) (k : Word) (f : Account → Account) (h : b ≠ a) :
    getAccountOptional (modifyState s a f) b = getAccountOptional s b ∧
    getStorage (modifyState s a f) b k = getStorage s b k ∧
    (modifyState s a f).codes = s.codes := by
  have spec := modifyState_spec s a f
  exact ⟨by simpa [h] using spec.1 b, by simpa [h] using spec.2.1 b k, spec.2.2⟩

example (s t : State) (a : Address) (k j v : Word) (h : j ≠ k)
    (success : setStorage s a k v = .ok t) :
    getStorage t a j = getStorage s a j := by
  have spec := setStorage_spec s t a k v success
  simpa [h] using spec.2.1 a j

example (s : State) (a : Address) (k : Word) (f : Account → Account)
    (nonempty : f (getAccount s a) ≠ emptyAccount) :
    getStorage (modifyState s a f) a k = getStorage s a k := by
  have spec := modifyState_spec s a f
  simpa [nonempty] using spec.2.1 a k

-- This program has the same write and destruction as the ordinary consumer.
def writeThenDestroy (s : State) (a : Address) (k v : Word) : Except StorageError State := do
  let t ← setStorage s a k v
  pure (destroyAccount t a)

example (s t : State) (a : Address) (k v : Word)
    (success : setStorage s a k v = .ok t) :
    writeThenDestroy s a k v = .ok (destroyAccount t a) ∧
    getAccountOptional (destroyAccount t a) a = none ∧
    (∀ j, getStorage (destroyAccount t a) a j = 0) ∧
    (∀ b, b ≠ a → getAccountOptional (destroyAccount t a) b = getAccountOptional s b) ∧
    (∀ b j, b ≠ a → getStorage (destroyAccount t a) b j = getStorage s b j) ∧
    (destroyAccount t a).codes = s.codes := by
  exact ⟨by simp [writeThenDestroy, success], write_then_destroy s t a k v success⟩

end WorldProof

namespace WorldProof

example (s : State) (a b : Address) (balance : Word) (code : ByteArray) (h : b ≠ a) :
    let t := setCode (incrementNonce (setAccountBalance s a balance) a) a code
    getAccountOptional t b = getAccountOptional s b ∧
    (∀ k, getStorage t b k = getStorage s b k) ∧
    (∀ hash, getCode t hash = if hash = emptyCodeHash then some ByteArray.empty
      else if hash = codeHash code then some code else getCode s hash) :=
  balance_nonce_code_off_target s a b balance code h

example (s : State) (a : Address) (code : ByteArray) :
    getCode (setCode s a code) (codeHash code) = some code ↔
      codeHash code ≠ emptyCodeHash ∨ code = ByteArray.empty :=
  setCode_getCode_written_iff s a code

example (code : ByteArray) :
    Word.ofBytesBE ⟨(EthLib.Cryptography.Hash.Keccak.keccak256 code).toArray⟩ =
      .ok (codeHash code) ∧
    Word.toBytesBE (codeHash code) =
      ⟨(EthLib.Cryptography.Hash.Keccak.keccak256 code).toArray⟩ := codeHash_bytes code

end WorldProof

namespace WorldProof

example (s : State) (a : Address) (balance : Word) (code : ByteArray) :
    let x := { getAccount s a with balance }
    let y := if x = emptyAccount then emptyAccount else x
    let result := setCode (incrementNonce (setAccountBalance s a balance) a) a code
    getAccountOptional result a = some { y with nonce := y.nonce + 1, codeHash := codeHash code } ∧
    (∀ k, getStorage result a k = if x = emptyAccount then 0 else getStorage s a k) :=
  balance_nonce_code_target_initial s a balance code

end WorldProof

namespace WorldProof

-- Apply every observation in the balance and nonce contracts at arbitrary keys.
example (s : State) (a b : Address) (k balance : Word) :
    let x := { getAccount s a with balance }
    getAccountOptional (setAccountBalance s a balance) b =
      (if b = a then (if x = emptyAccount then none else some x) else getAccountOptional s b) ∧
    getStorage (setAccountBalance s a balance) b k =
      (if b = a ∧ x = emptyAccount then 0 else getStorage s b k) ∧
    (setAccountBalance s a balance).codes = s.codes := by
  exact ⟨(setAccountBalance_spec s a balance).1 b,
    (setAccountBalance_spec s a balance).2.1 b k, (setAccountBalance_spec s a balance).2.2⟩

example (s : State) (a b : Address) (k : Word) :
    let x := { getAccount s a with nonce := (getAccount s a).nonce + 1 }
    getAccountOptional (incrementNonce s a) b =
      (if b = a then (if x = emptyAccount then none else some x) else getAccountOptional s b) ∧
    getStorage (incrementNonce s a) b k =
      (if b = a ∧ x = emptyAccount then 0 else getStorage s b k) ∧
    (incrementNonce s a).codes = s.codes := by
  exact ⟨(incrementNonce_spec s a).1 b, (incrementNonce_spec s a).2.1 b k,
    (incrementNonce_spec s a).2.2⟩

example (s : State) (a b : Address) (k hash : Word) (code : ByteArray) :
    let x := { getAccount s a with codeHash := codeHash code }
    getAccountOptional (setCode s a code) b =
      (if b = a then (if x = emptyAccount then none else some x) else getAccountOptional s b) ∧
    getStorage (setCode s a code) b k =
      (if b = a ∧ x = emptyAccount then 0 else getStorage s b k) ∧
    (setCode s a code).codes = (if codeHash code == emptyCodeHash then s.codes else
      (codeHash code, code) :: s.codes.filter (fun p => p.1 != codeHash code)) ∧
    getCode (setCode s a code) hash =
      (if hash = emptyCodeHash then some ByteArray.empty else
        if hash = codeHash code then some code else getCode s hash) := by
  have spec := setCode_spec s a code
  exact ⟨spec.1 b, spec.2.1 b k, spec.2.2, setCode_getCode s a code hash⟩

-- This branch is conditional on hash equality and does not infer code equality.
example (s : State) (a : Address) (code : ByteArray) (h : codeHash code = emptyCodeHash) :
    (setCode s a code).codes = s.codes ∧
    (getCode (setCode s a code) (codeHash code) = some code ↔ code = ByteArray.empty) := by
  constructor
  · simpa [h] using (setCode_spec s a code).2.2
  · simpa [h] using setCode_getCode_written_iff s a code

example (code : ByteArray) :
    codeHash code = BitVec.ofNat 256 (EthLib.Execution.Precompiles.Modexp.bytesToNat
      (EthLib.Cryptography.Hash.KeccakBits.keccak256 code).toArray.toList) ∧
    (codeHash code).toNat = EthLib.Execution.Precompiles.Modexp.bytesToNat
      (EthLib.Cryptography.Hash.Keccak.keccak256 code).toArray.toList :=
  ⟨codeHash_refinement code, codeHash_value code⟩

example (s : State) (a : Address) (balance : Word) (code : ByteArray) :
    let t := setCode (incrementNonce (setAccountBalance s a balance) a) a code
    t.codes = if codeHash code == emptyCodeHash then s.codes else
      (codeHash code, code) :: s.codes.filter (fun p => p.1 != codeHash code) :=
  (balance_nonce_code_target s a balance code).2.2

end WorldProof

namespace WorldProof

example (s : State) (a : Address) (code : ByteArray)
    (success : getCode (setCode s a code) (codeHash code) = some code) :
    codeHash code ≠ emptyCodeHash ∨ code = ByteArray.empty :=
  (setCode_getCode_written_iff s a code).mp success

example (s : State) (a : Address) (code : ByteArray)
    (condition : codeHash code ≠ emptyCodeHash ∨ code = ByteArray.empty) :
    getCode (setCode s a code) (codeHash code) = some code :=
  (setCode_getCode_written_iff s a code).mpr condition

end WorldProof
