/-!
# THE QUESTION AFTER THE COMMITMENT — FOUNDATION STONE TEST 16F

Runs in the Lean live editor with no imports (core Lean only).

Test 16E proved that a checked packet establishes derivability, not historical
occurrence.  Test 16F adds an interactive order:

1. the sender commits to a shared anchor;
2. only then, the receiving body chooses Y or Z;
3. the sender must answer from the committed anchor;
4. the receiver checks the answer independently.

Lean certifies:

* both challenges have valid responses;
* the two required endpoints differ;
* therefore NO single fixed replay endpoint answers both challenges;
* a response prepared for Y fails Z, and a response prepared for Z fails Y;
* the protocol transition system permits commitment, then challenge, then answer,
  and forbids skipping directly from commitment to a completed answer.

RED CONTROLS:

* the challenge space has only two elements, so a two-entry lookup table answers every
  challenge without waiting for it;
* an interactive transcript and a retrospectively fabricated transcript can be byte-for-
  byte identical.  Every transcript-only observer is blind to which history occurred.

Thus 16F earns a precise but restricted result: an after-commitment question defeats a
ONE-ANSWER replay.  It does not defeat complete precomputation, and a saved transcript
does not authenticate an historical interaction.  A stronger test needs a growing or
unbounded challenge family, or an external commitment/authentication primitive.
-/
namespace FoundationStoneSixteenF

/-! ## Exact geometry over Z[sqrt 3] -/

structure Z3 where
  a : Int
  b : Int
deriving DecidableEq

structure V3 where
  x : Z3
  y : Z3
  z : Z3
deriving DecidableEq

def zzero : Z3 := ⟨0, 0⟩
def zone : Z3 := ⟨1, 0⟩
def zadd (u v : Z3) : Z3 := ⟨u.a + v.a, u.b + v.b⟩
def zneg (u : Z3) : Z3 := ⟨-u.a, -u.b⟩
def zsub (u v : Z3) : Z3 := zadd u (zneg v)
def zscale (k : Int) (u : Z3) : Z3 := ⟨k * u.a, k * u.b⟩
def zroot (u : Z3) : Z3 := ⟨3 * u.b, u.a⟩

/-- Twice a 30-degree turn about z. -/
def rzP (v : V3) : V3 :=
  ⟨zsub (zroot v.x) v.y, zadd v.x (zroot v.y), zscale 2 v.z⟩

/-- Twice a 30-degree turn about y. -/
def ryP (v : V3) : V3 :=
  ⟨zadd (zroot v.x) v.z, zscale 2 v.y, zadd (zneg v.x) (zroot v.z)⟩

def anchor : V3 := ⟨zone, zzero, zzero⟩

/-! ## Commitment, challenge and response -/

structure Commitment where
  point : V3
deriving DecidableEq

def sealed : Commitment := ⟨anchor⟩

inductive Challenge
  | askY
  | askZ
deriving DecidableEq

def advance : Challenge → V3 → V3
  | .askY, v => ryP v
  | .askZ, v => rzP v

structure Response where
  endpoint : V3
deriving DecidableEq

def answer (c : Commitment) (q : Challenge) : Response := ⟨advance q c.point⟩

/-- The receiver accepts only the endpoint demanded by its challenge from the sealed
anchor. -/
def Accepts (c : Commitment) (q : Challenge) (r : Response) : Prop :=
  c = sealed ∧ r.endpoint = advance q c.point

instance (c : Commitment) (q : Challenge) (r : Response) : Decidable (Accepts c q r) := by
  unfold Accepts
  infer_instance

def check (c : Commitment) (q : Challenge) (r : Response) : Bool :=
  decide (Accepts c q r)

/-- 1. The responsive sender can answer either challenge from the same commitment. -/
theorem adaptive_answers_are_accepted :
    ∀ q, Accepts sealed q (answer sealed q) := by
  intro q
  exact ⟨rfl, rfl⟩

theorem checker_accepts_adaptive_answers :
    ∀ q, check sealed q (answer sealed q) = true := by
  intro q
  cases q <;> decide

/-! ## The challenge defeats a single fixed replay -/

theorem challenge_endpoints_are_different :
    (answer sealed .askY).endpoint ≠ (answer sealed .askZ).endpoint := by
  decide

/-- 2a. No one preselected endpoint is accepted for both questions. -/
theorem no_single_response_answers_both (r : Response) :
    ¬ (Accepts sealed .askY r ∧ Accepts sealed .askZ r) := by
  intro h
  have hy : r.endpoint = (answer sealed .askY).endpoint := h.1.2
  have hz : r.endpoint = (answer sealed .askZ).endpoint := h.2.2
  exact challenge_endpoints_are_different (hy.symm.trans hz)

/-- 2b. A replay prepared for Y is rejected when the receiver asks Z. -/
theorem y_replay_fails_z :
    check sealed .askZ (answer sealed .askY) = false := by
  decide

/-- 2c. A replay prepared for Z is rejected when the receiver asks Y. -/
theorem z_replay_fails_y :
    check sealed .askY (answer sealed .askZ) = false := by
  decide

theorem fixed_replay_control :
    check sealed .askY (answer sealed .askY) = true ∧
    check sealed .askZ (answer sealed .askY) = false ∧
    check sealed .askZ (answer sealed .askZ) = true ∧
    check sealed .askY (answer sealed .askZ) = false := by
  decide

/-! ## The protocol order is part of the state -/

inductive ProtocolState
  | open
  | committed (c : Commitment)
  | challenged (c : Commitment) (q : Challenge)
  | completed (c : Commitment) (q : Challenge) (r : Response)

/-- The two bodies alternate: sender commits, receiver challenges, sender answers. -/
inductive Step : ProtocolState → ProtocolState → Prop
  | sender_commits : Step .open (.committed sealed)
  | receiver_challenges (q) : Step (.committed sealed) (.challenged sealed q)
  | sender_answers (q) : Step (.challenged sealed q) (.completed sealed q (answer sealed q))

theorem ordered_protocol_runs : ∀ q,
    Step .open (.committed sealed) ∧
    Step (.committed sealed) (.challenged sealed q) ∧
    Step (.challenged sealed q) (.completed sealed q (answer sealed q)) := by
  intro q
  exact ⟨.sender_commits, .receiver_challenges q, .sender_answers q⟩

/-- 3a. The transition system has no direct commitment-to-completion step. -/
theorem cannot_answer_before_challenge (q : Challenge) (r : Response) :
    ¬ Step (.committed sealed) (.completed sealed q r) := by
  intro h
  cases h

/-- 3b. Nor can the receiver issue a challenge before the commitment exists. -/
theorem cannot_challenge_before_commitment (q : Challenge) :
    ¬ Step .open (.challenged sealed q) := by
  intro h
  cases h

/-! ## RED CONTROL 1: a complete lookup table defeats the finite challenge -/

abbrev ResponseTable := Challenge → Response

def completeTable : ResponseTable := fun q => answer sealed q

/-- 4a. Two stored answers cover the entire one-bit challenge space. -/
theorem complete_table_answers_every_challenge :
    ∀ q, Accepts sealed q (completeTable q) :=
  adaptive_answers_are_accepted

theorem complete_table_checker_green :
    ∀ q, check sealed q (completeTable q) = true :=
  checker_accepts_adaptive_answers

/-- The table really contains two different endpoints; it is not one answer in disguise. -/
theorem table_requires_both_branches :
    (completeTable .askY).endpoint ≠ (completeTable .askZ).endpoint :=
  challenge_endpoints_are_different

/-! ## RED CONTROL 2: a transcript still does not prove occurrence -/

structure Transcript where
  commitment : Commitment
  challenge : Challenge
  response : Response
deriving DecidableEq

def transcript (q : Challenge) : Transcript := ⟨sealed, q, answer sealed q⟩

def TranscriptValid (t : Transcript) : Prop :=
  Accepts t.commitment t.challenge t.response

instance (t : Transcript) : Decidable (TranscriptValid t) := by
  unfold TranscriptValid
  infer_instance

theorem recorded_transcripts_validate : ∀ q, TranscriptValid (transcript q) := by
  intro q
  exact adaptive_answers_are_accepted q

inductive History
  | interactive
  | fabricated
deriving DecidableEq

structure World where
  history : History
  record : Transcript
deriving DecidableEq

def interactiveWorld (q : Challenge) : World := ⟨.interactive, transcript q⟩
def fabricatedWorld (q : Challenge) : World := ⟨.fabricated, transcript q⟩

def InteractionOccurred (w : World) : Prop := w.history = .interactive

instance (w : World) : Decidable (InteractionOccurred w) := by
  unfold InteractionOccurred
  infer_instance

theorem interaction_occurs_only_in_first_world : ∀ q,
    InteractionOccurred (interactiveWorld q) ∧
    ¬ InteractionOccurred (fabricatedWorld q) := by
  intro q
  refine ⟨rfl, ?_⟩
  intro h
  cases h

/-- 5a. The stored transcripts are nevertheless identical. -/
theorem identical_transcript_different_history : ∀ q,
    (interactiveWorld q).record = (fabricatedWorld q).record ∧
    (interactiveWorld q).history ≠ (fabricatedWorld q).history := by
  intro q
  refine ⟨rfl, ?_⟩
  intro h
  cases h

/-- 5b. Every observer restricted to the transcript is blind to that difference. -/
theorem every_transcript_only_observer_is_blind {α : Type}
    (observer : Transcript → α) : ∀ q,
    observer (interactiveWorld q).record = observer (fabricatedWorld q).record := by
  intro q
  rfl

/-- 5c. In particular, validation accepts both stored records. -/
theorem validation_accepts_both_histories : ∀ q,
    TranscriptValid (interactiveWorld q).record ∧
    TranscriptValid (fabricatedWorld q).record := by
  intro q
  exact ⟨recorded_transcripts_validate q, recorded_transcripts_validate q⟩

/-! ## Certificate -/

theorem question_after_commitment_certificate :
    (∀ q, Accepts sealed q (answer sealed q)) ∧
    ((answer sealed .askY).endpoint ≠ (answer sealed .askZ).endpoint) ∧
    (∀ r, ¬ (Accepts sealed .askY r ∧ Accepts sealed .askZ r)) ∧
    (check sealed .askZ (answer sealed .askY) = false) ∧
    (check sealed .askY (answer sealed .askZ) = false) ∧
    (∀ q, Step .open (.committed sealed) ∧
      Step (.committed sealed) (.challenged sealed q) ∧
      Step (.challenged sealed q) (.completed sealed q (answer sealed q))) ∧
    (∀ q, Accepts sealed q (completeTable q)) ∧
    (∀ q, (interactiveWorld q).record = (fabricatedWorld q).record ∧
      (interactiveWorld q).history ≠ (fabricatedWorld q).history) ∧
    (∀ q, TranscriptValid (interactiveWorld q).record ∧
      TranscriptValid (fabricatedWorld q).record) :=
  ⟨adaptive_answers_are_accepted, challenge_endpoints_are_different,
   no_single_response_answers_both, y_replay_fails_z, z_replay_fails_y,
   ordered_protocol_runs, complete_table_answers_every_challenge,
   identical_transcript_different_history, validation_accepts_both_histories⟩

#print axioms adaptive_answers_are_accepted
#print axioms checker_accepts_adaptive_answers
#print axioms challenge_endpoints_are_different
#print axioms no_single_response_answers_both
#print axioms fixed_replay_control
#print axioms ordered_protocol_runs
#print axioms cannot_answer_before_challenge
#print axioms cannot_challenge_before_commitment
#print axioms complete_table_answers_every_challenge
#print axioms table_requires_both_branches
#print axioms recorded_transcripts_validate
#print axioms interaction_occurs_only_in_first_world
#print axioms identical_transcript_different_history
#print axioms every_transcript_only_observer_is_blind
#print axioms validation_accepts_both_histories
#print axioms question_after_commitment_certificate

end FoundationStoneSixteenF
