/-!
# THE UNBOUNDED CHALLENGE LADDER — FOUNDATION STONE TEST 16G

Runs in the Lean live editor with no imports (core Lean only).

Tests 16A–16F separated replay, signed evidence, proof-carrying evidence,
independent checking, and post-commitment challenge.  Test 16G asks what happens
when the receiver is not restricted to one fixed finite challenge set.

The process is the simplest exact helix.  Its unbounded height is read through a
twelve-seat clock.  A replay table records the prefix 0,...,K.  After that table
is fixed, the receiver asks for K+1.

Lean certifies:
1. At depth n the height is exactly n and the clock is n modulo 12.
2. For every finite prefix table, K+1 has no address in that table.
3. Its state is genuinely absent from the recorded range, not merely missing a
   label: height separates it from every recorded state.
4. Extending the table preserves every old answer and installs the former
   outside challenge as its new last entry.  The ladder can therefore be
   repeated without a final finite prefix.
5. RED CONTROL.  A total computable responder answers every challenge, including
   K+1.  Thus "outside recorded support" does NOT mean uncomputable,
   unpredictable, undecidable, or authenticated.  This test proves a boundary
   of finite replay, not a boundary of computation.

The mathematics is elementary (Nat successor and Fin bounds).  The contribution
of the test is the exact placement of that elementary fact in the helix/replay
protocol, with the overclaim blocked inside the certificate itself.
-/
namespace UnboundedChallengeLadder

abbrev Seat := Fin 12

/-- One point on the helix: unbounded height, twelve-seat circular shadow. -/
structure HelixState where
  height : Nat
  seat : Seat
deriving DecidableEq

def start : HelixState := ⟨0, 0⟩

/-- One climb: retain one unit of height while the shadow advances one seat. -/
def climb (s : HelixState) : HelixState := ⟨s.height + 1, s.seat + 1⟩

def iter : Nat → HelixState → HelixState
  | 0, s => s
  | n + 1, s => climb (iter n s)

/-- The live answer to the depth challenge n. -/
def answer (n : Nat) : HelixState := iter n start

/-- 1a. The helix remembers the full challenge depth. -/
theorem answer_height : ∀ n, (answer n).height = n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    change (answer n).height + 1 = n + 1
    rw [ih]

/-- 1b. The clock is only the height modulo twelve. -/
theorem answer_shadow : ∀ n, (answer n).seat.val = n % 12 := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    change ((answer n).seat + 1).val = (n + 1) % 12
    rw [Fin.val_add, ih]
    simp only [Fin.val_one]
    omega

/-- The circle can be home while the helix is not. -/
theorem twelve_clock_home_height_not :
    (answer 12).seat = (answer 0).seat ∧ answer 12 ≠ answer 0 := by
  decide

/-- A finite replay table containing exactly the prefix of depths 0,...,K. -/
structure ReplayTable where
  bound : Nat
  lookup : Fin (bound + 1) → HelixState

/-- The faithful table cut after depth K. -/
def recorded (K : Nat) : ReplayTable where
  bound := K
  lookup := fun i => answer i.val

theorem recorded_correct (K : Nat) (i : Fin ((recorded K).bound + 1)) :
    (recorded K).lookup i = answer i.val := rfl

/-- The receiver's next challenge is chosen only after seeing the table bound. -/
def nextChallenge (T : ReplayTable) : Nat := T.bound + 1

/-- 2. Every finite prefix exposes a valid next depth with no table address. -/
theorem next_challenge_is_outside (T : ReplayTable) :
    ¬ ∃ i : Fin (T.bound + 1), i.val = nextChallenge T := by
  intro h
  obtain ⟨i, hi⟩ := h
  have hil := i.isLt
  unfold nextChallenge at hi
  omega

/-- Different depths are different helix states, because their heights differ. -/
theorem different_depths_are_different (m n : Nat) (h : m ≠ n) :
    answer m ≠ answer n := by
  intro e
  have he := congrArg HelixState.height e
  rw [answer_height m, answer_height n] at he
  exact h he

/-- 3. The next answer is absent from the range of the faithful replay table. -/
theorem next_state_is_not_recorded (K : Nat) :
    ∀ i : Fin (K + 1), answer (K + 1) ≠ (recorded K).lookup i := by
  intro i
  change answer (K + 1) ≠ answer i.val
  apply different_depths_are_different
  omega

/-- Embed an old table address into the one-step-longer table. -/
def oldAddress {K : Nat} (i : Fin (K + 1)) : Fin ((K + 1) + 1) :=
  ⟨i.val, by omega⟩

/-- 4a. Extending the faithful replay preserves every recorded answer. -/
theorem extension_preserves_old (K : Nat) (i : Fin (K + 1)) :
    (recorded (K + 1)).lookup (oldAddress i) = (recorded K).lookup i := rfl

/-- The new last address in the extended table. -/
def newAddress (K : Nat) : Fin ((K + 1) + 1) := ⟨K + 1, by omega⟩

/-- 4b. Yesterday's outside challenge is today's new recorded entry. -/
theorem extension_records_the_challenge (K : Nat) :
    (recorded (K + 1)).lookup (newAddress K) =
      answer (nextChallenge (recorded K)) := rfl

/-- 4c. No finite prefix contains an address for every natural challenge. -/
theorem no_finite_prefix_covers_all (T : ReplayTable) :
    ¬ ∀ n : Nat, ∃ i : Fin (T.bound + 1), i.val = n := by
  intro hall
  exact next_challenge_is_outside T (hall (nextChallenge T))

/-! ## Red control: support is not computability -/

/-- A total live responder.  It computes rather than merely replaying a stored row. -/
def respond (n : Nat) : HelixState := answer n

/-- 5a. The live responder answers every natural challenge. -/
theorem total_responder_answers_every_depth : ∀ n, respond n = answer n :=
  fun _ => rfl

/-- 5b. In particular it answers the challenge outside any fixed replay table. -/
theorem responder_answers_outside (T : ReplayTable) :
    respond (nextChallenge T) = answer (nextChallenge T) := rfl

/-- 5c. The out-of-support answer is fully predictable: its height is the bound + 1. -/
theorem outside_answer_is_predictable (T : ReplayTable) :
    (respond (nextChallenge T)).height = T.bound + 1 := by
  rw [total_responder_answers_every_depth, answer_height]
  rfl

/-- The test's certificate.  Its final conjunct is the guardrail: finite replay
fails to contain the next answer while a computable responder still supplies it. -/
theorem unbounded_challenge_ladder_certificate :
    (∀ n, (answer n).height = n ∧ (answer n).seat.val = n % 12) ∧
    (∀ T : ReplayTable,
      ¬ ∃ i : Fin (T.bound + 1), i.val = nextChallenge T) ∧
    (∀ K, ∀ i : Fin (K + 1), answer (K + 1) ≠ (recorded K).lookup i) ∧
    (∀ K, ∀ i : Fin (K + 1),
      (recorded (K + 1)).lookup (oldAddress i) = (recorded K).lookup i) ∧
    (∀ K, (recorded (K + 1)).lookup (newAddress K) =
      answer (nextChallenge (recorded K))) ∧
    (∀ T : ReplayTable, respond (nextChallenge T) = answer (nextChallenge T)) :=
  ⟨fun n => ⟨answer_height n, answer_shadow n⟩,
   next_challenge_is_outside,
   next_state_is_not_recorded,
   extension_preserves_old,
   extension_records_the_challenge,
   responder_answers_outside⟩

#print axioms answer_height
#print axioms answer_shadow
#print axioms twelve_clock_home_height_not
#print axioms next_challenge_is_outside
#print axioms next_state_is_not_recorded
#print axioms extension_preserves_old
#print axioms extension_records_the_challenge
#print axioms no_finite_prefix_covers_all
#print axioms total_responder_answers_every_depth
#print axioms responder_answers_outside
#print axioms outside_answer_is_predictable
#print axioms unbounded_challenge_ladder_certificate

end UnboundedChallengeLadder
