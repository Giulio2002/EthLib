module

public import EthLib.EVM.World
import Mathlib.Tactic
public import EthLib.Cryptography.Proofs.Hash.KeccakBitsRefinement
public import EthLib.EVM.Proofs.Word

/-! Contracts for the pure account and storage state. -/

@[expose] public section
namespace EthLib.EVM.World

/-- An independent pointwise account-update specification. -/
def AccountUpdateSpec (before after : State) (address : Address)
    (value : Option Account) : Prop :=
  (∀ a, getAccountOptional after a = if a = address then value else getAccountOptional before a) ∧
  (∀ a k, getStorage after a k = getStorage before a k) ∧
  after.codes = before.codes

/-- An independent pointwise storage-update specification. -/
def StorageUpdateSpec (before after : State) (address : Address) (key value : Word) : Prop :=
  (∀ a, getAccountOptional after a = getAccountOptional before a) ∧
  (∀ a k, getStorage after a k =
    if a = address ∧ k = key then value else getStorage before a k) ∧
  after.codes = before.codes

private theorem lookup_filter_ne {α β : Type} [BEq α] [LawfulBEq α]
    (xs : List (α × β)) (a b : α) (h : a ≠ b) :
    (xs.filter (fun p => p.1 != b)).lookup a = xs.lookup a := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨k, v⟩
    by_cases hk : k = b <;> by_cases ha : a = k <;>
      simp_all [List.lookup_cons, beq_eq_false_iff_ne.mpr h]

private theorem lookup_filter_same {α β : Type} [BEq α] [LawfulBEq α]
    (xs : List (α × β)) (a : α) :
    (xs.filter (fun p => p.1 != a)).lookup a = none := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨k, v⟩
    by_cases hk : k = a
    · subst k
      simpa only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ite_false] using ih
    · have hb : (k != a) = true := bne_iff_ne.mpr hk
      have ha : (a == k) = false := beq_eq_false_iff_ne.mpr (Ne.symm hk)
      simp [hb, List.lookup_cons, ha, ih]


/-- Setting an account has the pointwise effect of replacing one entry. -/
theorem setAccount_spec (s : State) (a : Address) (v : Option Account) :
    AccountUpdateSpec s (setAccount s a v) a v := by
  refine ⟨?_, ?_, rfl⟩
  · intro b
    by_cases h : b = a
    · subst b
      cases v <;> simp [getAccountOptional, setAccount, lookup_filter_same]
    · have hb : (b == a) = false := beq_eq_false_iff_ne.mpr h
      cases v <;> simp [getAccountOptional, setAccount, List.lookup_cons, h, hb, lookup_filter_ne _ _ _ h]
  · intro b k
    rfl

/-- Account existence is exactly the presence of an account. -/
theorem accountExists_iff (s : State) (a : Address) :
    accountExists s a = true ↔ ∃ x, getAccountOptional s a = some x := by
  simp [accountExists, Option.isSome_iff_exists]

/-- Empty and absent accounts remain distinct. -/
theorem accountExistsAndIsEmpty_iff (s : State) (a : Address) :
    accountExistsAndIsEmpty s a = true ↔ getAccountOptional s a = some emptyAccount := by
  simp [accountExistsAndIsEmpty]

/-- The only storage-write error is absence of the account. -/
theorem setStorage_error_iff (s : State) (a : Address) (k v : Word) :
    setStorage s a k v = .error .missingAccount ↔ getAccountOptional s a = none := by
  simp [setStorage, accountExists]

/-- A successful storage write satisfies the pointwise update equations. -/
theorem setStorage_spec (s t : State) (a : Address) (k v : Word)
    (h : setStorage s a k v = .ok t) : StorageUpdateSpec s t a k v := by
  unfold setStorage at h
  split at h
  next present =>
    simp only [Except.ok.injEq] at h
    subst t
    refine ⟨?_, ?_, rfl⟩
    · intro b
      rfl
    · intro b j
      by_cases same : (b, j) = (a, k)
      · have hb : b = a := congrArg Prod.fst same
        have hj : j = k := congrArg Prod.snd same
        subst b
        subst j
        by_cases zero : v = 0
        · subst v
          simp [getStorage, lookup_filter_same]
        · have z : v ≠ 0#256 := by simpa using zero
          simp [getStorage, z]
      · have hp : ¬(b = a ∧ j = k) := by simpa [Prod.mk.injEq] using same
        have hb : ((b, j) == (a, k)) = false := beq_eq_false_iff_ne.mpr same
        by_cases zero : v = 0
        · subst v
          simp [getStorage, hp, lookup_filter_ne _ _ _ same]
        · have z : v ≠ 0#256 := by simpa using zero
          simp [getStorage, z, hp, List.lookup_cons, hb, lookup_filter_ne _ _ _ same]
  next absent => simp at h

/-- Presence is sufficient for an actual successful storage write. -/
theorem setStorage_success_iff (s : State) (a : Address) (k v : Word) :
    (∃ t, setStorage s a k v = .ok t) ↔ ∃ x, getAccountOptional s a = some x := by
  cases h : getAccountOptional s a <;> simp [setStorage, accountExists, h]

private theorem lookup_clear_same (xs : List ((Address × Word) × Word))
    (a : Address) (k : Word) :
    (xs.filter (fun p => p.1.1 != a)).lookup (a, k) = none := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨⟨b, j⟩, v⟩
    by_cases h : b = a
    · subst b
      simpa using ih
    · have hb : ((a, k) == (b, j)) = false :=
        beq_eq_false_iff_ne.mpr (by intro e; exact h (congrArg Prod.fst e).symm)
      simp [h, List.lookup_cons, hb, ih]

private theorem lookup_clear_other (xs : List ((Address × Word) × Word))
    (a b : Address) (k : Word) (h : b ≠ a) :
    (xs.filter (fun p => p.1.1 != a)).lookup (b, k) = xs.lookup (b, k) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨⟨c, j⟩, v⟩
    by_cases hc : c = a
    · subst c
      have hb : ((b, k) == (a, j)) = false :=
        beq_eq_false_iff_ne.mpr (by intro e; exact h (congrArg Prod.fst e))
      simp [List.lookup_cons, hb, ih]
    · simp [hc, List.lookup_cons, ih]

/-- Clearing storage changes no accounts or code and clears exactly one address. -/
theorem destroyStorage_spec (s : State) (a : Address) :
    (∀ b, getAccountOptional (destroyStorage s a) b = getAccountOptional s b) ∧
    (∀ b k, getStorage (destroyStorage s a) b k =
      if b = a then 0 else getStorage s b k) ∧
    (destroyStorage s a).codes = s.codes := by
  refine ⟨?_, ?_, rfl⟩
  · intro b; rfl
  · intro b k
    by_cases h : b = a
    · subst b
      simp [getStorage, destroyStorage, lookup_clear_same]
    · simp [getStorage, destroyStorage, h, lookup_clear_other _ _ _ _ h]

/-- Destruction removes the account and clears exactly its storage. -/
theorem destroyAccount_spec (s : State) (a : Address) :
    (∀ b, getAccountOptional (destroyAccount s a) b =
      if b = a then none else getAccountOptional s b) ∧
    (∀ b k, getStorage (destroyAccount s a) b k =
      if b = a then 0 else getStorage s b k) ∧
    (destroyAccount s a).codes = s.codes := by
  have ac := setAccount_spec (destroyStorage s a) a none
  have st := destroyStorage_spec s a
  refine ⟨?_, ?_, ?_⟩
  · intro b
    change getAccountOptional (setAccount (destroyStorage s a) a none) b = _
    rw [ac.1 b, st.1 b]
  · intro b k
    change getStorage (setAccount (destroyStorage s a) a none) b k = _
    rw [ac.2.1 b k, st.2.1 b k]
  · exact ac.2.2.trans st.2.2

/-- The account update either keeps its nonempty result or destroys the empty result. -/
theorem modifyState_spec (s : State) (a : Address) (f : Account → Account) :
    (∀ b, getAccountOptional (modifyState s a f) b =
      if b = a then (if f (getAccount s a) = emptyAccount then none
        else some (f (getAccount s a))) else getAccountOptional s b) ∧
    (∀ b k, getStorage (modifyState s a f) b k =
      if b = a ∧ f (getAccount s a) = emptyAccount then 0 else getStorage s b k) ∧
    (modifyState s a f).codes = s.codes := by
  let x := f (getAccount s a)
  let t := setAccount s a (some x)
  have ht := setAccount_spec s a (some x)
  have hat : getAccountOptional t a = some x := by simpa [t] using ht.1 a
  have et : accountExistsAndIsEmpty t a = true ↔ x = emptyAccount := by
    rw [accountExistsAndIsEmpty_iff, hat]
    simp
  change (∀ b, getAccountOptional (if accountExistsAndIsEmpty t a then destroyAccount t a else t) b =
    if b = a then (if x = emptyAccount then none else some x) else getAccountOptional s b) ∧
    (∀ b k, getStorage (if accountExistsAndIsEmpty t a then destroyAccount t a else t) b k =
      if b = a ∧ x = emptyAccount then 0 else getStorage s b k) ∧
    (if accountExistsAndIsEmpty t a then destroyAccount t a else t).codes = s.codes
  by_cases h : x = emptyAccount
  · have he : accountExistsAndIsEmpty t a = true := et.mpr h
    simp only [he, ↓reduceIte]
    have hd := destroyAccount_spec t a
    refine ⟨?_, ?_, ?_⟩
    · intro b
      rw [hd.1 b, ht.1 b]
      by_cases hb : b = a <;> simp [h, hb]
    · intro b k
      rw [hd.2.1 b k, ht.2.1 b k]
      by_cases hb : b = a <;> simp [h, hb]
    · exact hd.2.2.trans ht.2.2
  · have he : accountExistsAndIsEmpty t a = false := by
      cases hbool : accountExistsAndIsEmpty t a with
      | false => rfl
      | true => exact False.elim (h (et.mp hbool))
    simp only [he, Bool.false_eq_true, ↓reduceIte]
    refine ⟨?_, ?_, ht.2.2⟩
    · intro b
      simpa [h] using ht.1 b
    · intro b k
      simpa [h] using ht.2.1 b k

/-- Account and storage queries agree, and the code lists are literally equal.

This is stronger than agreement of code queries for lists with duplicate keys.
-/
def ObservationallyEqual (s t : State) : Prop :=
  (∀ a, getAccountOptional s a = getAccountOptional t a) ∧
  (∀ a k, getStorage s a k = getStorage t a k) ∧ s.codes = t.codes

/-- A second account write overwrites the first at the same address. -/
theorem setAccount_overwrite (s : State) (a : Address) (x y : Option Account) :
    ObservationallyEqual (setAccount (setAccount s a x) a y) (setAccount s a y) := by
  have h₁ := setAccount_spec s a x
  have h₂ := setAccount_spec (setAccount s a x) a y
  have h₃ := setAccount_spec s a y
  refine ⟨?_, ?_, h₂.2.2.trans (h₁.2.2.trans h₃.2.2.symm)⟩
  · intro b
    rw [h₂.1 b, h₃.1 b, h₁.1 b]
    split <;> simp_all
  · intro b k
    rw [h₂.2.1 b k, h₁.2.1 b k, h₃.2.1 b k]

/-- Account writes at distinct addresses commute observationally. -/
theorem setAccount_commute (s : State) (a b : Address) (x y : Option Account)
    (different : a ≠ b) :
    ObservationallyEqual (setAccount (setAccount s a x) b y)
      (setAccount (setAccount s b y) a x) := by
  have h₁ := setAccount_spec s a x
  have h₂ := setAccount_spec (setAccount s a x) b y
  have h₃ := setAccount_spec s b y
  have h₄ := setAccount_spec (setAccount s b y) a x
  refine ⟨?_, ?_, h₂.2.2.trans (h₁.2.2.trans (h₃.2.2.symm.trans h₄.2.2.symm))⟩
  · intro c
    rw [h₂.1 c, h₄.1 c, h₁.1 c, h₃.1 c]
    by_cases ha : c = a <;> by_cases hb : c = b <;> simp_all
  · intro c k
    rw [h₂.2.1 c k, h₁.2.1 c k, h₄.2.1 c k, h₃.2.1 c k]

/-- A write followed by destruction clears the address and preserves other state. -/
theorem write_then_destroy (s t : State) (a : Address) (k v : Word)
    (success : setStorage s a k v = .ok t) :
    getAccountOptional (destroyAccount t a) a = none ∧
    (∀ j, getStorage (destroyAccount t a) a j = 0) ∧
    (∀ b, b ≠ a → getAccountOptional (destroyAccount t a) b = getAccountOptional s b) ∧
    (∀ b j, b ≠ a → getStorage (destroyAccount t a) b j = getStorage s b j) ∧
    (destroyAccount t a).codes = s.codes := by
  have write := setStorage_spec s t a k v success
  have destroy := destroyAccount_spec t a
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa using destroy.1 a
  · intro j
    simpa using destroy.2.1 a j
  · intro b h
    rw [destroy.1 b]
    simp [h, write.1 b]
  · intro b j h
    rw [destroy.2.1 b j, write.2.1 b j]
    simp [h]
  · exact destroy.2.2.trans write.2.2

/-- Account absence means no entry in the finite representation has that key. -/
theorem getAccountOptional_none_iff (s : State) (a : Address) :
    getAccountOptional s a = none ↔ ∀ p ∈ s.accounts, a ≠ p.1 := by
  simp [getAccountOptional]

/-- A present account is the first entry for its address. -/
theorem getAccountOptional_some_iff (s : State) (a : Address) (x : Account) :
    getAccountOptional s a = some x ↔
      ∃ before after, s.accounts = before ++ (a, x) :: after ∧
        ∀ p ∈ before, a ≠ p.1 := by
  simpa [getAccountOptional] using (List.lookup_eq_some_iff (l := s.accounts) (k := a) (b := x))

/-- Storage reads use the first matching entry, with zero for absence. -/
theorem getStorage_spec (s : State) (a : Address) (k v : Word) :
    getStorage s a k = v ↔
      (v = 0 ∧ ∀ p ∈ s.storage, (a, k) ≠ p.1) ∨
      (∃ before after, s.storage = before ++ ((a, k), v) :: after ∧
        ∀ p ∈ before, (a, k) ≠ p.1) := by
  cases h : s.storage.lookup (a, k) with
  | none =>
    have hn := (List.lookup_eq_none_iff (l := s.storage) (k := (a, k))).mp h
    constructor
    · intro hv
      left
      have hv' : (0 : Word) = v := by simpa [getStorage, h] using hv
      exact ⟨hv'.symm, by simpa using hn⟩
    · intro hv
      rcases hv with ⟨hv, _⟩ | ⟨before, after, hs, hb⟩
      · simp [getStorage, h, hv]
      · have hv : s.storage.lookup (a, k) = some v :=
          List.lookup_eq_some_iff.mpr ⟨before, after, hs, by simpa using hb⟩
        rw [h] at hv
        contradiction
  | some x =>
    have hx := (List.lookup_eq_some_iff (l := s.storage) (k := (a, k)) (b := x)).mp h
    constructor
    · intro hv
      have : x = v := by simpa [getStorage, h] using hv
      subst x
      exact Or.inr (by simpa using hx)
    · intro hv
      rcases hv with ⟨_, hn⟩ | ⟨before, after, hs, hn⟩
      · have hn' : s.storage.lookup (a, k) = none :=
          List.lookup_eq_none_iff.mpr (by simpa using hn)
        simp [h] at hn'
      · have hv : s.storage.lookup (a, k) = some v :=
          List.lookup_eq_some_iff.mpr ⟨before, after, hs, by simpa using hn⟩
        rw [h] at hv
        cases hv
        simp [getStorage, h]

/-- A defaulting account lookup has exactly the source's two cases. -/
theorem getAccount_spec (s : State) (a : Address) :
    (getAccountOptional s a = none → getAccount s a = emptyAccount) ∧
    (∀ x, getAccountOptional s a = some x → getAccount s a = x) := by
  cases h : getAccountOptional s a <;> simp [getAccount, h]

/-- The empty code hash always resolves to empty bytes. -/
theorem getCode_empty (s : State) : getCode s emptyCodeHash = some ByteArray.empty := by
  simp [getCode]

/-- A nonempty hash is looked up in the separately supplied code store. -/
theorem getCode_nonempty (s : State) (h : Word) (hne : h ≠ emptyCodeHash) :
    getCode s h = s.codes.lookup h := by
  simp [getCode, hne]

/-- Whenever an account exists, an actual write realizes the update specification. -/
theorem setStorage_realizes (s : State) (a : Address) (k v : Word)
    (present : ∃ x, getAccountOptional s a = some x) :
    ∃ t, setStorage s a k v = .ok t ∧ StorageUpdateSpec s t a k v := by
  obtain ⟨t, ht⟩ := (setStorage_success_iff s a k v).2 present
  exact ⟨t, ht, setStorage_spec s t a k v ht⟩

/-- A successful zero write removes every physical entry for the slot. -/
theorem setStorage_zero_removes (s t : State) (a : Address) (k : Word)
    (success : setStorage s a k 0 = .ok t) :
    ∀ p ∈ t.storage, p.1 ≠ (a, k) := by
  unfold setStorage at success
  split at success
  next _ =>
    simp only [Except.ok.injEq] at success
    subst t
    intro p hp
    have hp' : p ∈ s.storage.filter (fun p => p.1 != (a, k)) := by
      simpa using hp
    have := (List.mem_filter.mp hp').2
    exact bne_iff_ne.mp this
  next _ => simp at success

/-- Two successful writes to the same slot expose the last value. -/
theorem setStorage_overwrite (s t u w : State) (a : Address) (k x y : Word)
    (first : setStorage s a k x = .ok t)
    (second : setStorage t a k y = .ok u)
    (direct : setStorage s a k y = .ok w) : ObservationallyEqual u w := by
  have h₁ := setStorage_spec s t a k x first
  have h₂ := setStorage_spec t u a k y second
  have h₃ := setStorage_spec s w a k y direct
  refine ⟨?_, ?_, h₂.2.2.trans (h₁.2.2.trans h₃.2.2.symm)⟩
  · intro b
    rw [h₂.1 b, h₁.1 b, h₃.1 b]
  · intro b j
    rw [h₂.2.1 b j, h₃.2.1 b j, h₁.2.1 b j]
    by_cases h : b = a ∧ j = k <;> simp [h]

/-- Successful writes to distinct address-slot pairs commute observationally. -/
theorem setStorage_commute (s t u v w : State) (a b : Address) (k j x y : Word)
    (different : (a, k) ≠ (b, j))
    (first : setStorage s a k x = .ok t) (second : setStorage t b j y = .ok u)
    (third : setStorage s b j y = .ok v) (fourth : setStorage v a k x = .ok w) :
    ObservationallyEqual u w := by
  have h₁ := setStorage_spec s t a k x first
  have h₂ := setStorage_spec t u b j y second
  have h₃ := setStorage_spec s v b j y third
  have h₄ := setStorage_spec v w a k x fourth
  refine ⟨?_, ?_, h₂.2.2.trans (h₁.2.2.trans (h₃.2.2.symm.trans h₄.2.2.symm))⟩
  · intro c
    rw [h₂.1 c, h₁.1 c, h₄.1 c, h₃.1 c]
  · intro c i
    rw [h₂.2.1 c i, h₄.2.1 c i, h₁.2.1 c i, h₃.2.1 c i]
    split_ifs <;> simp_all [Prod.ext_iff]

/-- Balance replacement follows the account cleanup contract. -/
theorem setAccountBalance_spec (s : State) (a : Address) (balance : Word) :
    (∀ b, getAccountOptional (setAccountBalance s a balance) b =
      if b = a then (if { getAccount s a with balance } = emptyAccount then none
        else some { getAccount s a with balance }) else getAccountOptional s b) ∧
    (∀ b k, getStorage (setAccountBalance s a balance) b k =
      if b = a ∧ { getAccount s a with balance } = emptyAccount then 0 else getStorage s b k) ∧
    (setAccountBalance s a balance).codes = s.codes :=
  modifyState_spec s a _

/-- Nonce increment follows the account cleanup contract. -/
theorem incrementNonce_spec (s : State) (a : Address) :
    (∀ b, getAccountOptional (incrementNonce s a) b =
      if b = a then (if { getAccount s a with nonce := (getAccount s a).nonce + 1 } = emptyAccount
        then none else some { getAccount s a with nonce := (getAccount s a).nonce + 1 })
      else getAccountOptional s b) ∧
    (∀ b k, getStorage (incrementNonce s a) b k =
      if b = a ∧ { getAccount s a with nonce := (getAccount s a).nonce + 1 } = emptyAccount
      then 0 else getStorage s b k) ∧
    (incrementNonce s a).codes = s.codes :=
  modifyState_spec s a _

/-- The code hash uses the independently refined whole sponge. -/
theorem codeHash_refinement (code : ByteArray) :
    codeHash code = BitVec.ofNat 256 (EthLib.Execution.Precompiles.Modexp.bytesToNat
      (EthLib.Cryptography.Hash.KeccakBits.keccak256 code).toArray.toList) := by
  unfold codeHash
  rw [EthLib.Cryptography.Hash.KeccakBits.keccak256_eq]

/-- The digest decodes to the hash word and round-trips byte for byte. -/
theorem codeHash_bytes (code : ByteArray) :
    let bytes : ByteArray := ⟨(EthLib.Cryptography.Hash.Keccak.keccak256 code).toArray⟩
    Word.ofBytesBE bytes = .ok (codeHash code) ∧
    Word.toBytesBE (codeHash code) = bytes := by
  have h : Word.ofBytesBE ⟨(EthLib.Cryptography.Hash.Keccak.keccak256 code).toArray⟩ =
      .ok (codeHash code) := by
    have size : (⟨(EthLib.Cryptography.Hash.Keccak.keccak256 code).toArray⟩ : ByteArray).size = 32 :=
      (EthLib.Cryptography.Hash.Keccak.keccak256 code).size_toArray
    simp [Word.ofBytesBE, codeHash, size]
  exact ⟨h, EthLib.EVM.Proofs.Word.toBytesBE_ofBytesBE _ _ h⟩

/-- Account and storage observations and the exact code list after a code write. -/
theorem setCode_spec (s : State) (a : Address) (code : ByteArray) :
    let hash := codeHash code
    let stored := if hash == emptyCodeHash then s.codes else
      (hash, code) :: s.codes.filter (fun p => p.1 != hash)
    (∀ b, getAccountOptional (setCode s a code) b =
      if b = a then (if { getAccount s a with codeHash := hash } = emptyAccount then none
        else some { getAccount s a with codeHash := hash }) else getAccountOptional s b) ∧
    (∀ b k, getStorage (setCode s a code) b k =
      if b = a ∧ { getAccount s a with codeHash := hash } = emptyAccount
      then 0 else getStorage s b k) ∧
    (setCode s a code).codes = stored := by
  dsimp only
  unfold setCode
  dsimp only
  split
  · exact modifyState_spec s a _
  · have h := modifyState_spec { s with codes :=
        (codeHash code, code) :: s.codes.filter (fun p => p.1 != codeHash code) } a
        (fun account => { account with codeHash := codeHash code })
    dsimp only [getAccount, getAccountOptional, getStorage] at h ⊢
    exact h

/-- Every code query after insertion, including an arbitrary preexisting store. -/
theorem setCode_getCode (s : State) (a : Address) (code : ByteArray) (hash : Word) :
    getCode (setCode s a code) hash =
      if hash = emptyCodeHash then some ByteArray.empty
      else if hash = codeHash code then some code else getCode s hash := by
  have h := (setCode_spec s a code).2.2
  unfold getCode
  rw [h]
  by_cases he : hash = emptyCodeHash
  · simp [he]
  · by_cases hc : codeHash code = emptyCodeHash
    · simp [he, hc]
    · by_cases hh : hash = codeHash code
      · simp [hc, hh]
      · have hb : (hash == codeHash code) = false := beq_eq_false_iff_ne.mpr hh
        simp [he, hc, hh, List.lookup_cons, lookup_filter_ne _ _ _ hh, hb]

/-- The getter returns the written bytes exactly under these conditions. -/
theorem setCode_getCode_written_iff (s : State) (a : Address) (code : ByteArray) :
    getCode (setCode s a code) (codeHash code) = some code ↔
      codeHash code ≠ emptyCodeHash ∨ code = ByteArray.empty := by
  rw [setCode_getCode]
  by_cases h : codeHash code = emptyCodeHash <;> simp [h, eq_comm]

/-- The digest word has the exact big-endian numeric value of all 32 bytes. -/
theorem codeHash_value (code : ByteArray) :
    (codeHash code).toNat = EthLib.Execution.Precompiles.Modexp.bytesToNat
      (EthLib.Cryptography.Hash.Keccak.keccak256 code).toArray.toList := by
  exact ((EthLib.EVM.Proofs.Word.ofBytesBE_ok_iff _ _).mp (codeHash_bytes code).1).2

/-- A balance, nonce and code program preserves every other address. -/
theorem balance_nonce_code_off_target (s : State) (a b : Address) (balance : Word)
    (code : ByteArray) (h : b ≠ a) :
    let result := setCode (incrementNonce (setAccountBalance s a balance) a) a code
    getAccountOptional result b = getAccountOptional s b ∧
    (∀ k, getStorage result b k = getStorage s b k) ∧
    (∀ hash, getCode result hash =
      if hash = emptyCodeHash then some ByteArray.empty
      else if hash = codeHash code then some code else getCode s hash) := by
  dsimp only
  have hb := setAccountBalance_spec s a balance
  have hn := incrementNonce_spec (setAccountBalance s a balance) a
  have hc := setCode_spec (incrementNonce (setAccountBalance s a balance) a) a code
  refine ⟨?_, ?_, ?_⟩
  · rw [hc.1 b, hn.1 b, hb.1 b]
    simp [h]
  · intro k
    rw [hc.2.1 b k, hn.2.1 b k, hb.2.1 b k]
    simp [h]
  · intro hash
    rw [setCode_getCode]
    have codes : (incrementNonce (setAccountBalance s a balance) a).codes = s.codes :=
      hn.2.2.trans hb.2.2
    simp only [getCode, codes]

/-- The program's target account and storage include cleanup at every step. -/
theorem balance_nonce_code_target (s : State) (a : Address) (balance : Word)
    (code : ByteArray) :
    let first := setAccountBalance s a balance
    let second := incrementNonce first a
    let result := setCode second a code
    let x := { getAccount s a with balance }
    let y := { getAccount first a with nonce := (getAccount first a).nonce + 1 }
    let z := { getAccount second a with codeHash := codeHash code }
    getAccountOptional result a = (if z = emptyAccount then none else some z) ∧
    (∀ k, getStorage result a k =
      if z = emptyAccount ∨ y = emptyAccount ∨ x = emptyAccount then 0 else getStorage s a k) ∧
    result.codes = if codeHash code == emptyCodeHash then s.codes else
      (codeHash code, code) :: s.codes.filter (fun p => p.1 != codeHash code) := by
  dsimp only
  have hb := setAccountBalance_spec s a balance
  have hn := incrementNonce_spec (setAccountBalance s a balance) a
  have hc := setCode_spec (incrementNonce (setAccountBalance s a balance) a) a code
  refine ⟨?_, ?_, ?_⟩
  · simpa using hc.1 a
  · intro k
    rw [hc.2.1 a k, hn.2.1 a k, hb.2.1 a k]
    simp only [true_and]
    split_ifs <;> simp_all
  · rw [hc.2.2, hn.2.2, hb.2.2]

private theorem balance_get (s : State) (a : Address) (balance : Word) :
    getAccount (setAccountBalance s a balance) a =
      if { getAccount s a with balance } = emptyAccount then emptyAccount
      else { getAccount s a with balance } := by
  change (getAccountOptional (setAccountBalance s a balance) a).getD emptyAccount = _
  rw [(setAccountBalance_spec s a balance).1 a]
  simp only [↓reduceIte]
  split <;> rfl

private theorem nonce_get (s : State) (a : Address) :
    getAccount (incrementNonce s a) a =
      { getAccount s a with nonce := (getAccount s a).nonce + 1 } := by
  change (getAccountOptional (incrementNonce s a) a).getD emptyAccount = _
  rw [(incrementNonce_spec s a).1 a]
  have ne : { getAccount s a with nonce := (getAccount s a).nonce + 1 } ≠ emptyAccount := by
    intro eq
    have n := congrArg Account.nonce eq
    simp [emptyAccount] at n
  simp [ne]

/-- The composed target is expressed only in terms of the initial account. -/
theorem balance_nonce_code_target_initial (s : State) (a : Address) (balance : Word) (code : ByteArray) :
    let x := { getAccount s a with balance }
    let y := if x = emptyAccount then emptyAccount else x
    let result := setCode (incrementNonce (setAccountBalance s a balance) a) a code
    getAccountOptional result a = some { y with nonce := y.nonce + 1, codeHash := codeHash code } ∧
    (∀ k, getStorage result a k = if x = emptyAccount then 0 else getStorage s a k) := by
  dsimp only
  have hn := nonce_get (setAccountBalance s a balance) a
  have hb := balance_get s a balance
  have hx := balance_nonce_code_target s a balance code
  dsimp only at hx
  rw [hn, hb] at hx
  have ne (x : Account) : { x with nonce := x.nonce + 1, codeHash := codeHash code } ≠ emptyAccount := by
    intro eq
    have n := congrArg Account.nonce eq
    simp [emptyAccount] at n
  have ne2 (x : Account) : { x with nonce := x.nonce + 1 } ≠ emptyAccount := by
    intro eq
    have n := congrArg Account.nonce eq
    simp [emptyAccount] at n
  simp only [ne, ne2, ↓reduceIte, false_or] at hx
  exact ⟨hx.1, hx.2.1⟩

end EthLib.EVM.World
