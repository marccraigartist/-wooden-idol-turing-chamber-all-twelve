/-!
# THE FOUNDATION STONE — TEST 2Y: THE CLOCK IS A SMALL FLICKER

Runs in the Lean live editor with no imports (core Lean only). Input to Test 3.

Order of results:
1. GENERAL. If two readings both reverse under the flip, the second is the first
   compared with a STABLE reading. So once one reversing reading exists, every other
   reversing reading is "that one, shifted by something still": the moving layer is
   the still layer plus a single orientation.
2. THE CLOCK. Magenta sorts the twelve seats into six pairs. The chart picks one seat
   from each pair, and magenta keeps the pair and turns the chart over. Pair plus chart
   pins down the seat. So the clock with magenta IS six pairs × {truth, discovery}
   with the flip on the second coordinate: the Stage 2 Flicker (ℕ × Bool), with six
   addresses instead of infinitely many.
3. THE (4 7) SWAP IS THE STILL SHIFT. Parity is the chart shifted by the reading
   "this seat is B4 or B7", and that reading is still under magenta.
4. ONLY RELATIONS ARE STILL. Under magenta every seat changes chart, yet the agreement
   between chart and parity never changes at any seat.

Seat `0` is B12; seats `1`–`11` are B1–B11. Magenta is `k ↦ 11 − k`.
-/
namespace SmallFlicker

/-- 1. Two reversing readings: the second is the first compared with a still reading. -/
theorem reversing_is_orientation_plus_still {X : Type} (T : X → X) (P Q : X → Bool)
    (hP : ∀ x, P (T x) = !P x) (hQ : ∀ x, Q (T x) = !Q x) :
    ∃ S : X → Bool, (∀ x, S (T x) = S x) ∧ ∀ x, Q x = (P x == S x) := by
  refine ⟨fun x => Q x == P x, fun x => ?_, fun x => ?_⟩
  · show (Q (T x) == P (T x)) = (Q x == P x)
    rw [hQ, hP]
    generalize Q x = q
    generalize P x = p
    cases q <;> cases p <;> rfl
  · show Q x = (P x == (Q x == P x))
    generalize Q x = q
    generalize P x = p
    cases q <;> cases p <;> rfl

/-! ## The clock -/

abbrev Seat := Fin 12

def magenta (k : Seat) : Seat := 11 - k

/-- The truth chart {B1, B3, B4, B5, B9, B11}. -/
def truthChart (k : Seat) : Bool :=
  match k.val with
  | 1 | 3 | 4 | 5 | 9 | 11 => true
  | _ => false

/-- Parity: the odd seats. -/
def odd (k : Seat) : Bool := k.val % 2 == 1

/-- Which magenta pair a seat belongs to: 0 to 5. -/
def pairOf (k : Seat) : Nat := if k.val ≤ 5 then k.val else 11 - k.val

/-- The reading "this seat is B4 or B7". -/
def fourSeven (k : Seat) : Bool := k.val == 4 || k.val == 7

/-- 2a. There are six pairs. -/
theorem six_pairs : ∀ k : Seat, pairOf k < 6 := by decide

/-- 2b. Magenta keeps the pair... -/
theorem magenta_keeps_the_pair : ∀ k : Seat, pairOf (magenta k) = pairOf k := by decide

/-- 2c. ...and turns the chart over. -/
theorem magenta_turns_the_chart : ∀ k : Seat, truthChart (magenta k) = !truthChart k := by
  decide

/-- 2d. Pair and chart together pin down the seat: the clock is six pairs × two sides. -/
theorem pair_and_chart_pin_the_seat :
    ∀ a b : Seat, pairOf a = pairOf b → truthChart a = truthChart b → a = b := by
  decide

/-- 3a. "B4 or B7" is still under magenta... -/
theorem four_seven_is_still : ∀ k : Seat, fourSeven (magenta k) = fourSeven k := by decide

/-- 3b. ...and parity is the chart shifted by it: the (4 7) swap is the still shift. -/
theorem parity_is_chart_shifted_by_four_seven :
    ∀ k : Seat, odd k = (truthChart k != fourSeven k) := by decide

/-- 4. Every seat changes chart under magenta, but the chart–parity agreement never
changes: only relations are still. -/
theorem only_relations_are_still :
    (∀ k : Seat, truthChart (magenta k) ≠ truthChart k) ∧
    (∀ k : Seat, (truthChart (magenta k) == odd (magenta k)) = (truthChart k == odd k)) := by
  decide

theorem small_flicker_certificate :
    (∀ k : Seat, pairOf (magenta k) = pairOf k) ∧
    (∀ k : Seat, truthChart (magenta k) = !truthChart k) ∧
    (∀ a b : Seat, pairOf a = pairOf b → truthChart a = truthChart b → a = b) ∧
    (∀ k : Seat, odd k = (truthChart k != fourSeven k)) ∧
    (∀ k : Seat, fourSeven (magenta k) = fourSeven k) :=
  ⟨magenta_keeps_the_pair, magenta_turns_the_chart, pair_and_chart_pin_the_seat,
   parity_is_chart_shifted_by_four_seven, four_seven_is_still⟩

#print axioms reversing_is_orientation_plus_still
#print axioms magenta_keeps_the_pair
#print axioms magenta_turns_the_chart
#print axioms pair_and_chart_pin_the_seat
#print axioms four_seven_is_still
#print axioms parity_is_chart_shifted_by_four_seven
#print axioms only_relations_are_still
#print axioms small_flicker_certificate

end SmallFlicker
