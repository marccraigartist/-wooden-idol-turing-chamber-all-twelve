/-!
# THE FOUNDATION STONE — TEST 8X: DIRECTION FROM THE TWO SHARED LINES

Runs in the Lean live editor with no imports (core Lean only). Input to Test 8.

Test 7 derives the antipode from three premises: the frame change keeps the shared
forward step, is reciprocal, and is separate. Here the frame change is again an
ARBITRARY map of the twelve seats, and the premises are replaced by two lines of Marc's
own clock:

* the RELAY line (magenta, `k ↦ 11 − k`) is the same line for both bodies;
* the DONE/DOING axis (the 12–6 line, `k ↦ −k`) is the same line for both bodies;
* and no seat is shared (separation).

Order of results:
1. Sharing both lines forces the shared forward step: the turn (relay, then the
   done/doing axis) is `k ↦ k + 1`, and the frame change commutes with it.
2. Hence the frame change is a rotation by its value at B12.
3. Sharing the done/doing axis leaves only offset 0 or 6.
4. Separation leaves the antipode. Reciprocity is not assumed: it follows.
5. Red controls: sharing only the relay line admits magenta itself; sharing only the
   done/doing axis admits a separate, reciprocal map that is not the antipode.

Seat `0` is B12; seats `1`–`11` are B1–B11.
-/
namespace SharedLines

abbrev Seat := Fin 12

def relay (k : Seat) : Seat := 11 - k
def doneAxis (k : Seat) : Seat := 0 - k

/-- A frame change keeps a line when it carries that mirror to itself. -/
def KeepsLine (f : Seat → Seat) (m : Seat → Seat) : Prop := ∀ k, f (m k) = m (f k)

/-- 1a. The turn: relay, then the done/doing axis, is one seat forward. -/
theorem the_turn_is_one_forward : ∀ k : Seat, doneAxis (relay k) = k + 1 := by decide

/-- 1b. Keeping both lines keeps the forward step. -/
theorem both_lines_keep_forward (f : Seat → Seat)
    (hr : KeepsLine f relay) (hd : KeepsLine f doneAxis) :
    ∀ k, f (k + 1) = f k + 1 := by
  intro k
  rw [← the_turn_is_one_forward k, hd, hr, the_turn_is_one_forward]

/-- 2. Keeping the forward step forces a rotation by the value at B12. -/
theorem forward_forces_rotation (f : Seat → Seat) (h : ∀ k, f (k + 1) = f k + 1) :
    ∀ k : Seat, f k = k + f 0 := by
  have step : ∀ n (hn : n < 12), f ⟨n, hn⟩ = ⟨n, hn⟩ + f 0 := by
    intro n
    induction n with
    | zero => intro hn; apply Fin.ext; simp
    | succ n ih =>
      intro hn
      have hprev := ih (by omega)
      have hsucc : (⟨n + 1, hn⟩ : Seat) = ⟨n, by omega⟩ + 1 := by
        apply Fin.ext; simp [Fin.val_add]; omega
      rw [hsucc, h, hprev]
      apply Fin.ext
      simp [Fin.val_add]
      omega
  intro k
  exact step k.val k.isLt

/-- 3. Keeping the done/doing axis leaves offset 0 or 6. -/
theorem axis_leaves_zero_or_six (f : Seat → Seat) (hd : KeepsLine f doneAxis) :
    f 0 = 0 ∨ f 0 = 6 := by
  have h := hd 0
  have e : doneAxis 0 = 0 := by decide
  rw [e] at h
  revert h
  unfold doneAxis
  generalize f 0 = t
  revert t
  decide

/-- 4. The main result: both shared lines plus separation force the antipode. -/
theorem shared_lines_force_antipode (f : Seat → Seat)
    (hr : KeepsLine f relay) (hd : KeepsLine f doneAxis) (hs : ∀ k, f k ≠ k) :
    ∀ k, f k = k + 6 := by
  have hrot := forward_forces_rotation f (both_lines_keep_forward f hr hd)
  have hsix : f 0 = 6 := by
    rcases axis_leaves_zero_or_six f hd with h0 | h6
    · exact absurd h0 (hs 0)
    · exact h6
  intro k
  rw [hrot k, hsix]

/-- 4'. So B's B1 is A's B7, and reciprocity comes free. -/
theorem shared_lines_earn_B1_B7_and_reciprocity (f : Seat → Seat)
    (hr : KeepsLine f relay) (hd : KeepsLine f doneAxis) (hs : ∀ k, f k ≠ k) :
    f 1 = 7 ∧ ∀ k, f (f k) = k := by
  have h := shared_lines_force_antipode f hr hd hs
  refine ⟨by rw [h]; decide, fun k => ?_⟩
  rw [h, h]
  revert k
  decide

/-- 5a. Red control: sharing only the relay line admits magenta itself. -/
theorem relay_alone_admits_magenta :
    KeepsLine relay relay ∧ (∀ k, relay k ≠ k) ∧ relay 1 ≠ 7 := by
  unfold KeepsLine
  decide

/-- A separate, reciprocal map that keeps the done/doing axis but is not the antipode:
B12↔B6, B1↔B2, B11↔B10, B3↔B4, B9↔B8, B5↔B7. -/
def axisOnly (k : Seat) : Seat :=
  match k.val with
  | 0 => 6 | 6 => 0
  | 1 => 2 | 2 => 1 | 11 => 10 | 10 => 11
  | 3 => 4 | 4 => 3 | 9 => 8 | 8 => 9
  | 5 => 7 | _ => 5

/-- 5b. Red control: sharing only the done/doing axis is not enough. -/
theorem axis_alone_admits_another :
    KeepsLine axisOnly doneAxis ∧ (∀ k, axisOnly k ≠ k) ∧
    (∀ k, axisOnly (axisOnly k) = k) ∧ axisOnly 1 ≠ 7 := by
  unfold KeepsLine
  decide

#print axioms the_turn_is_one_forward
#print axioms both_lines_keep_forward
#print axioms forward_forces_rotation
#print axioms axis_leaves_zero_or_six
#print axioms shared_lines_force_antipode
#print axioms shared_lines_earn_B1_B7_and_reciprocity
#print axioms relay_alone_admits_magenta
#print axioms axis_alone_admits_another

end SharedLines
