import FoundationStoneTest16BI
import FoundationStoneTest16AM

/-!
# THE TURING CHAMBER — TEST 16BJ: THE PRIME-PACKED SEMANTIC LAYER

Lean 4.35.0-rc2 / pinned Mathlib.

This is Layer B2 at its semantic boundary.  A primitive five-counter state is
encoded in one natural number

  2^C0 * 3^C1 * 5^C2 * 7^C3 * 11^C4,

with the second physical counter zero.  The packed macro transition performs
exact multiplication, exact division, and divisibility branching.

Lean proves that encoding commutes with every primitive five-counter
instruction (`inc`, `dec/zero`, and explicit `halt`), obtains a genuine
`Respects` theorem, and lifts it to halting equivalence.  The next layer must
refine each packed macro operation to the already-verified finite primitive
MM2 blocks.  This file does not disguise those macro operations as MM2.
-/

namespace FoundationStoneTest16BJ

abbrev Reg5 := Fin 5

def prime (i : Reg5) : Nat :=
  if i = 0 then 2 else if i = 1 then 3 else if i = 2 then 5 else
  if i = 3 then 7 else 11

def fromVec (c : Reg5 → Nat) : FoundationStoneTest16AM.FiveCounters :=
  ⟨c 0, c 1, c 2, c 3, c 4⟩

theorem pack_update_inc (c : Reg5 → Nat) (i : Reg5) :
    FoundationStoneTest16AM.pack
        (fromVec (Function.update c i (c i + 1))) =
      prime i * FoundationStoneTest16AM.pack (fromVec c) := by
  have h := FoundationStoneTest16AM.increment_laws (fromVec c)
  fin_cases i
  · simpa [fromVec, Function.update, prime, FoundationStoneTest16AM.inc0] using h.1
  · simpa [fromVec, Function.update, prime, FoundationStoneTest16AM.inc1] using h.2.1
  · simpa [fromVec, Function.update, prime, FoundationStoneTest16AM.inc2] using h.2.2.1
  · simpa [fromVec, Function.update, prime, FoundationStoneTest16AM.inc3] using h.2.2.2.1
  · simpa [fromVec, Function.update, prime, FoundationStoneTest16AM.incT] using h.2.2.2.2

theorem prime_dvd_pack_iff (c : Reg5 → Nat) (i : Reg5) :
    prime i ∣ FoundationStoneTest16AM.pack (fromVec c) ↔ 0 < c i := by
  fin_cases i
  · simpa [prime, fromVec] using FoundationStoneTest16AM.two_dvd_iff (fromVec c)
  · simpa [prime, fromVec] using FoundationStoneTest16AM.three_dvd_iff (fromVec c)
  · simpa [prime, fromVec] using FoundationStoneTest16AM.five_dvd_iff (fromVec c)
  · simpa [prime, fromVec] using FoundationStoneTest16AM.seven_dvd_iff (fromVec c)
  · simpa [prime, fromVec] using FoundationStoneTest16AM.eleven_dvd_iff (fromVec c)

theorem pack_update_dec (c : Reg5 → Nat) (i : Reg5) (h : 0 < c i) :
    FoundationStoneTest16AM.pack
        (fromVec (Function.update c i (c i - 1))) =
      FoundationStoneTest16AM.pack (fromVec c) / prime i := by
  fin_cases i
  · simpa [fromVec, Function.update, prime, FoundationStoneTest16AM.dec0] using
      FoundationStoneTest16AM.decrement_laws (fromVec c) h
  · simpa [fromVec, Function.update, prime, FoundationStoneTest16AM.dec1] using
      FoundationStoneTest16AM.decrement_laws_1 (fromVec c) h
  · simpa [fromVec, Function.update, prime, FoundationStoneTest16AM.dec2] using
      FoundationStoneTest16AM.decrement_laws_2 (fromVec c) h
  · simpa [fromVec, Function.update, prime, FoundationStoneTest16AM.dec3] using
      FoundationStoneTest16AM.decrement_laws_3 (fromVec c) h
  · simpa [fromVec, Function.update, prime, FoundationStoneTest16AM.decT] using
      FoundationStoneTest16AM.decrement_laws_T (fromVec c) h

structure PackedState (L : Type) where
  pc : L
  a : Nat
  b : Nat
deriving Repr

def encode {L : Type} (s : FoundationStoneTest16AY.State 5 L) : PackedState L :=
  ⟨s.pc, FoundationStoneTest16AM.pack (fromVec s.counters), 0⟩

/-- Semantic packed transition.  These arithmetic operations are its
specification; 16AV/16AW and their linked successors must implement them. -/
def packedStep {L : Type} (P : L → FoundationStoneTest16AY.Instr 5 L) :
    PackedState L → Option (PackedState L)
  | s =>
    match P s.pc with
    | .halt => none
    | .inc i next => some ⟨next, prime i * s.a, s.b⟩
    | .dec i positive zero =>
        if prime i ∣ s.a then some ⟨positive, s.a / prime i, s.b⟩
        else some ⟨zero, s.a, s.b⟩

theorem packed_step_encode {L : Type}
    (P : L → FoundationStoneTest16AY.Instr 5 L)
    (s : FoundationStoneTest16AY.State 5 L) :
    packedStep P (encode s) =
      (FoundationStoneTest16AY.step P s).map encode := by
  cases hi : P s.pc with
  | halt => simp [packedStep, encode, FoundationStoneTest16AY.step, hi]
  | inc i next =>
      simp only [packedStep, encode, FoundationStoneTest16AY.step, hi, Option.map_some,
        FoundationStoneTest16AY.setCounter]
      rw [pack_update_inc]
  | dec i positive zero =>
      by_cases hz : s.counters i = 0
      · have hnd : ¬ prime i ∣ FoundationStoneTest16AM.pack (fromVec s.counters) := by
          rw [prime_dvd_pack_iff]
          omega
        simp [packedStep, encode, FoundationStoneTest16AY.step, hi, hz, hnd]
      · have hp : 0 < s.counters i := Nat.pos_of_ne_zero hz
        have hd : prime i ∣ FoundationStoneTest16AM.pack (fromVec s.counters) :=
          (prime_dvd_pack_iff s.counters i).2 hp
        simp only [packedStep, encode, FoundationStoneTest16AY.step, hi, hd,
          ↓reduceIte, hz, Option.map_some, FoundationStoneTest16AY.setCounter]
        rw [pack_update_dec _ i hp]

def Encodes {L : Type} (s : FoundationStoneTest16AY.State 5 L)
    (t : PackedState L) : Prop := encode s = t

theorem primitive_five_respects_packed {L : Type}
    (P : L → FoundationStoneTest16AY.Instr 5 L) :
    StateTransition.Respects (FoundationStoneTest16AY.step P)
      (packedStep P) Encodes := by
  intro s t hst
  subst t
  cases hs : FoundationStoneTest16AY.step P s with
  | none =>
      calc
        packedStep P (encode s) =
            (FoundationStoneTest16AY.step P s).map encode := packed_step_encode P s
        _ = none := by rw [hs]; rfl
  | some s' =>
      refine ⟨encode s', rfl, Relation.TransGen.single ?_⟩
      calc
        packedStep P (encode s) =
            (FoundationStoneTest16AY.step P s).map encode := packed_step_encode P s
        _ = some (encode s') := by rw [hs]; rfl

def FiveTerminates {L : Type} (P : L → FoundationStoneTest16AY.Instr 5 L)
    (s : FoundationStoneTest16AY.State 5 L) : Prop :=
  (StateTransition.eval (FoundationStoneTest16AY.step P) s).Dom

def PackedTerminates {L : Type} (P : L → FoundationStoneTest16AY.Instr 5 L)
    (s : PackedState L) : Prop :=
  (StateTransition.eval (packedStep P) s).Dom

theorem packed_halting_iff {L : Type}
    (P : L → FoundationStoneTest16AY.Instr 5 L)
    (s : FoundationStoneTest16AY.State 5 L) :
    FiveTerminates P s ↔ PackedTerminates P (encode s) := by
  unfold FiveTerminates PackedTerminates
  exact (StateTransition.tr_eval_dom (primitive_five_respects_packed P) rfl).symm

/-! Red control inherited from the arithmetic layer: non-coprime bases do not
encode independent logical counters injectively. -/
theorem noncoprime_red_control :
    ¬ Function.Injective (fun p : Nat × Nat => FoundationStoneTest16AM.badPack p.1 p.2) :=
  FoundationStoneTest16AM.noncoprime_not_injective

theorem turing_chamber_16BJ_certificate :
    (∀ {L : Type} (P : L → FoundationStoneTest16AY.Instr 5 L),
      StateTransition.Respects (FoundationStoneTest16AY.step P)
        (packedStep P) Encodes) ∧
    (∀ {L : Type} (P : L → FoundationStoneTest16AY.Instr 5 L)
      (s : FoundationStoneTest16AY.State 5 L),
      FiveTerminates P s ↔ PackedTerminates P (encode s)) ∧
    ¬ Function.Injective
      (fun p : Nat × Nat => FoundationStoneTest16AM.badPack p.1 p.2) :=
  ⟨primitive_five_respects_packed, packed_halting_iff, noncoprime_red_control⟩

#print axioms pack_update_inc
#print axioms prime_dvd_pack_iff
#print axioms pack_update_dec
#print axioms packed_step_encode
#print axioms primitive_five_respects_packed
#print axioms packed_halting_iff
#print axioms turing_chamber_16BJ_certificate

end FoundationStoneTest16BJ
