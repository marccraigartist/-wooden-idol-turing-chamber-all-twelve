import Mathlib

/-!
# THE PRICE OF PROVENANCE — FOUNDATION STONE TEST 16R

Imports Mathlib for finite-cardinality reasoning.

Test 16O proved that an A→B transfer followed by B→A preserves total mass but
does not restore the original ownership split.  Test 16R asks exactly how much
extra memory is required to make that restoration possible.

The naked endpoint after the round trip is `(a+b, 0)`.  It remembers the total
but forgets which of its units began at A and which began at B.  For a fixed
total `T`, there are exactly `T+1` possible original splits:

    (0,T), (1,T-1), ..., (T,0).

Lean certifies:

1. any successful recovery scheme must distinguish all `T+1` splits;
2. therefore a memory alphabet with `K` states can recover every split of
   total `T` only if `T+1 ≤ K`;
3. no fixed finite memory alphabet works for arbitrary totals;
4. in particular, no memory and one relay bit both fail;
5. the lower bound is exact: the dependent memory `Fin (T+1)`, storing A's
   original share, restores every split of total `T`;
6. equivalently, one unbounded natural-number register is sufficient;
7. labelled tokens give the richer, unit-level version: transport may change
   every holder while leaving every origin unchanged.

The relay's occupied/empty bit from 16O is operational memory, not provenance
memory.  It preserves mass during one primitive transfer but cannot remember
an arbitrarily large ownership partition.  The minimum provenance capacity is
not a fixed number of bits: for total `T` it is exactly `T+1` distinguishable
states (thus its bit cost grows with `T`).
-/

namespace FoundationStoneTest16R

/-! ## 1. Naked transfer forgets the split -/

structure Split where
  a : Nat
  b : Nat
deriving DecidableEq, Repr

def total (s : Split) : Nat := s.a + s.b

/-- The naked A→B→A endpoint: all mass is at A and only the total survives. -/
def nakedRoundTrip (s : Split) : Split := ⟨total s, 0⟩

theorem naked_round_trip_conserves_total (s : Split) :
    total (nakedRoundTrip s) = total s := by
  simp [total, nakedRoundTrip]

/-- A concrete collision: two distinct histories have the same naked endpoint. -/
theorem naked_collision :
    (⟨0, 1⟩ : Split) ≠ ⟨1, 0⟩ ∧
    nakedRoundTrip ⟨0, 1⟩ = nakedRoundTrip ⟨1, 0⟩ := by
  decide

/-! ## 2. Abstract provenance memory -/

/-- `remember` is written before provenance is erased; `recover` sees only the
merged total and that memory. -/
def Restores (M : Type) (remember : Split → M) (recover : Nat → M → Split) : Prop :=
  ∀ s, recover (total s) (remember s) = s

/-- The split indexed by `i` among the `T+1` splits of total `T`. -/
def splitAt (T : Nat) (i : Fin (T + 1)) : Split := ⟨i.val, T - i.val⟩

theorem splitAt_total (T : Nat) (i : Fin (T + 1)) :
    total (splitAt T i) = T := by
  change i.val + (T - i.val) = T
  omega

theorem splitAt_injective (T : Nat) : Function.Injective (splitAt T) := by
  intro i j h
  have ha := congrArg Split.a h
  apply Fin.ext
  exact ha

/-- Recovery forces the memory to be injective on every fixed-total fibre. -/
theorem recovery_forces_fibre_injective {M : Type} (remember : Split → M)
    (recover : Nat → M → Split) (h : Restores M remember recover) (T : Nat) :
    Function.Injective (fun i : Fin (T + 1) => remember (splitAt T i)) := by
  intro i j hij
  have hi := h (splitAt T i)
  have hj := h (splitAt T j)
  rw [splitAt_total] at hi hj
  change remember (splitAt T i) = remember (splitAt T j) at hij
  rw [hij] at hi
  apply splitAt_injective T
  rw [← hi, hj]

/-! ## 3. Exact lower bound: `T+1` memory states -/

/-- A `K`-state memory can recover every split of total `T` only if `T+1 ≤ K`. -/
theorem finite_memory_lower_bound (T K : Nat) (remember : Split → Fin K)
    (recover : Nat → Fin K → Split) (h : Restores (Fin K) remember recover) :
    T + 1 ≤ K := by
  have hinj := recovery_forces_fibre_injective remember recover h T
  have hcard := Fintype.card_le_of_injective
    (fun i : Fin (T + 1) => remember (splitAt T i)) hinj
  simpa using hcard

/-- No fixed finite alphabet can recover arbitrary ownership splits.  Its own
size `K` already supplies a total with `K+1` competing histories. -/
theorem no_fixed_finite_memory (K : Nat) (remember : Split → Fin K)
    (recover : Nat → Fin K → Split) :
    ¬ Restores (Fin K) remember recover := by
  intro h
  have bad := finite_memory_lower_bound K K remember recover h
  omega

/-- Zero provenance states cannot even begin a universal recovery scheme. -/
theorem no_memory_fails (remember : Split → Fin 1)
    (recover : Nat → Fin 1 → Split) :
    ¬ Restores (Fin 1) remember recover :=
  no_fixed_finite_memory 1 remember recover

/-- One Boolean-sized relay bit (two states) also fails universally. -/
theorem one_bit_fails (remember : Split → Fin 2)
    (recover : Nat → Fin 2 → Split) :
    ¬ Restores (Fin 2) remember recover :=
  no_fixed_finite_memory 2 remember recover

/-- More sharply, one bit already fails on total two, because that fibre has
the three splits `(0,2)`, `(1,1)`, `(2,0)`. -/
theorem one_bit_fails_at_total_two (remember : Split → Fin 2)
    (recover : Nat → Fin 2 → Split) (h : Restores (Fin 2) remember recover) :
    False := by
  have bad := finite_memory_lower_bound 2 2 remember recover h
  omega

/-! ## 4. Matching upper bound -/

/-- The canonical provenance mark for a split: A's original share.  Its type
contains exactly `total s + 1` states. -/
def exactMark (s : Split) : Fin (total s + 1) :=
  ⟨s.a, by unfold total; omega⟩

/-- Recover the corresponding split in the fixed-total fibre. -/
def exactRecover (T : Nat) (mark : Fin (T + 1)) : Split := splitAt T mark

theorem exact_memory_restores (s : Split) :
    exactRecover (total s) (exactMark s) = s := by
  rcases s with ⟨a, b⟩
  simp [exactRecover, exactMark, splitAt, total]

/-- Hence the lower bound is tight: exactly `T+1` states suffice for total `T`. -/
theorem exact_capacity_is_sufficient (T : Nat) :
    ∀ i : Fin (T + 1), exactRecover T i = splitAt T i := by
  intro i
  rfl

/-- A non-dependent implementation can store the same information in one
unbounded natural-number register. -/
def rememberA (s : Split) : Nat := s.a

def recoverFromA (T a : Nat) : Split := ⟨a, T - a⟩

theorem one_unbounded_register_restores :
    Restores Nat rememberA recoverFromA := by
  intro s
  rcases s with ⟨a, b⟩
  simp [recoverFromA, rememberA, total]

/-! ## 5. Labelled tokens: unit-level provenance -/

abbrev Body := Bool

/-- A token has both a current holder and an immutable origin. -/
structure Token where
  origin : Body
  holder : Body
deriving DecidableEq, Repr

def relocate (newHolder : Body) (t : Token) : Token :=
  { t with holder := newHolder }

def relocateAll (newHolder : Body) (tokens : List Token) : List Token :=
  tokens.map (relocate newHolder)

def ownerLedger (tokens : List Token) : List Body := tokens.map Token.origin

theorem relocation_preserves_each_origin (newHolder : Body) (t : Token) :
    (relocate newHolder t).origin = t.origin := rfl

theorem relocation_preserves_the_ledger (newHolder : Body) (tokens : List Token) :
    ownerLedger (relocateAll newHolder tokens) = ownerLedger tokens := by
  simp [ownerLedger, relocateAll, relocate]

/-- Seed `a` A-origin tokens and `b` B-origin tokens in their original bodies. -/
def seedTokens (a b : Nat) : List Token :=
  List.replicate a ⟨false, false⟩ ++ List.replicate b ⟨true, true⟩

def restoreFromLedger (ledger : List Body) : Split :=
  ⟨ledger.count false, ledger.count true⟩

theorem seed_ledger_recovers_split (a b : Nat) :
    restoreFromLedger (ownerLedger (seedTokens a b)) = ⟨a, b⟩ := by
  simp [restoreFromLedger, ownerLedger, seedTokens, List.count_replicate]

/-- After moving every token to B and then every token back to A, holder
information has merged, but the origin ledger still restores the split. -/
theorem labelled_round_trip_restores (a b : Nat) :
    restoreFromLedger
      (ownerLedger (relocateAll false (relocateAll true (seedTokens a b)))) =
      ⟨a, b⟩ := by
  rw [relocation_preserves_the_ledger, relocation_preserves_the_ledger]
  exact seed_ledger_recovers_split a b

/-- Concrete red/green control: all three tokens finish held by A, while their
origins still read A,A,B and recover the original split `(2,1)`. -/
theorem concrete_labelled_control :
    (relocateAll false (relocateAll true (seedTokens 2 1))).map Token.holder =
      [false, false, false] ∧
    ownerLedger (relocateAll false (relocateAll true (seedTokens 2 1))) =
      [false, false, true] ∧
    restoreFromLedger
      (ownerLedger (relocateAll false (relocateAll true (seedTokens 2 1)))) =
      ⟨2, 1⟩ := by
  decide

/-! ## Certificate -/

theorem price_of_provenance_certificate :
    (∀ T K remember recover, Restores (Fin K) remember recover → T + 1 ≤ K) ∧
    (∀ K remember recover, ¬ Restores (Fin K) remember recover) ∧
    (∀ remember recover, ¬ Restores (Fin 2) remember recover) ∧
    (∀ s, exactRecover (total s) (exactMark s) = s) ∧
    Restores Nat rememberA recoverFromA ∧
    (∀ newHolder tokens,
      ownerLedger (relocateAll newHolder tokens) = ownerLedger tokens) ∧
    (∀ a b,
      restoreFromLedger
        (ownerLedger (relocateAll false (relocateAll true (seedTokens a b)))) =
        ⟨a, b⟩) :=
  ⟨finite_memory_lower_bound, no_fixed_finite_memory, one_bit_fails,
   exact_memory_restores, one_unbounded_register_restores,
   relocation_preserves_the_ledger, labelled_round_trip_restores⟩

#print axioms naked_collision
#print axioms recovery_forces_fibre_injective
#print axioms finite_memory_lower_bound
#print axioms no_fixed_finite_memory
#print axioms one_bit_fails
#print axioms one_bit_fails_at_total_two
#print axioms exact_memory_restores
#print axioms one_unbounded_register_restores
#print axioms relocation_preserves_the_ledger
#print axioms seed_ledger_recovers_split
#print axioms labelled_round_trip_restores
#print axioms concrete_labelled_control
#print axioms price_of_provenance_certificate

end FoundationStoneTest16R
