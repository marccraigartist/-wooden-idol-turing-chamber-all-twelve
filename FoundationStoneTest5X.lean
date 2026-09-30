/-!
# THE FOUNDATION STONE — TEST 5X: WHERE FORGERY SHOWS

Runs in the Lean live editor with no imports (core Lean only). An audit of Charlie's
Test 5, rebuilt from its own definitions (`antipode k = k + 6`, `Genuine`, the
relabel-only forgery), but asked at EVERY seat instead of one.

Charlie's `forged_frame_is_rejected` checks one message: Truth, from body A, at B1.
Here the same forgery — change the source to B, leave the sentence untranslated — is
tried at all twelve seats.

Order of results:
1. The relabel-only forgery of a Truth message is caught at exactly four seats,
   B1, B4, B7, B10: the weld square (seat number ≡ 1 mod 3). At the other eight
   seats it passes as genuine.
2. That is forced by the (4 7) swap: the antipode keeps parity, so the chart and its
   antipode disagree only at B4, B7 and their antipodes B10, B1.
3. A reading that the antipode leaves unchanged (parity, for instance) can never
   catch the forgery at any seat.
4. The smallest language closed under both the body change (+6) and magenta needs
   exactly four charts: A's Truth, A's Discovery, B's Truth, B's Discovery. They are
   all different, and each move sends each to one of the four. Charlie's language
   (every one of the 4096 seat-readings) is far larger than the two-body exchange needs.

Seat `0` is B12; seats `1`–`11` are B1–B11.
-/
namespace WhereForgeryShows

abbrev Seat := Fin 12

def truthChart (k : Seat) : Bool :=
  match k.val with
  | 1 | 3 | 4 | 5 | 9 | 11 => true
  | _ => false

def odd (k : Seat) : Bool := k.val % 2 == 1

def antipode (k : Seat) : Seat := k + 6
def magenta (k : Seat) : Seat := 11 - k

inductive Body
  | A
  | B
deriving DecidableEq

def inLocalFrame : Body → Seat → Seat
  | .A, k => k
  | .B, k => antipode k

/-- A message about one seat: source body, a seat-reading in that body's language,
the seat in the shared A-frame, and the answer. -/
structure Message where
  source : Body
  reading : Seat → Bool
  seat : Seat
  answer : Bool

/-- Charlie's check: the answer matches the reading, evaluated in the source's frame. -/
def Genuine (m : Message) : Prop := m.answer = m.reading (inLocalFrame m.source m.seat)

/-- The genuine Truth message from A at seat `k`. -/
def truthFromA (k : Seat) : Message := ⟨.A, truthChart, k, truthChart k⟩

/-- The relabel-only forgery: claim it came from B, translate nothing. -/
def relabel (m : Message) : Message := { m with source := .B }

theorem truthFromA_genuine (k : Seat) : Genuine (truthFromA k) := rfl

/-- 1. The forgery is caught exactly on the weld square. -/
theorem forgery_caught_exactly_on_the_weld_square :
    ∀ k : Seat, ¬ Genuine (relabel (truthFromA k)) ↔ k.val % 3 = 1 := by
  unfold Genuine relabel truthFromA inLocalFrame antipode
  decide

/-- 1'. Named seat by seat: B1, B4, B7, B10. -/
theorem the_weld_square_is_B1_B4_B7_B10 :
    ∀ k : Seat, k.val % 3 = 1 ↔ (k = 1 ∨ k = 4 ∨ k = 7 ∨ k = 10) := by
  decide

/-- 1''. So at eight seats the forgery passes as genuine. -/
theorem forgery_passes_off_the_weld_square :
    ∀ k : Seat, k.val % 3 ≠ 1 → Genuine (relabel (truthFromA k)) := by
  unfold Genuine relabel truthFromA inLocalFrame antipode
  decide

/-- 2. Why: the antipode keeps parity, so only the (4 7) swap and its antipodes show. -/
theorem antipode_keeps_parity : ∀ k : Seat, odd (antipode k) = odd k := by decide

/-- 3. A reading the antipode leaves unchanged never catches the forgery. -/
theorem still_readings_never_catch_forgery (r : Seat → Bool)
    (hr : ∀ k, r (antipode k) = r k) (k : Seat) :
    Genuine (relabel ⟨.A, r, k, r k⟩) := by
  show r k = r (antipode k)
  rw [hr]

/-- The four charts. -/
def chartA (k : Seat) : Bool := truthChart k
def discA (k : Seat) : Bool := !truthChart k
def chartB (k : Seat) : Bool := truthChart (antipode k)
def discB (k : Seat) : Bool := !truthChart (antipode k)

/-- 4a. The four charts are all different. -/
theorem four_different_charts :
    (∃ k : Seat, chartA k ≠ chartB k) ∧ (∃ k : Seat, chartA k ≠ discB k) ∧
    (∃ k : Seat, discA k ≠ chartB k) ∧ (∃ k : Seat, discA k ≠ discB k) := by
  decide

/-- 4b. The body change swaps A's charts with B's... -/
theorem body_change_swaps_the_charts :
    ∀ k : Seat, chartA (antipode k) = chartB k ∧ chartB (antipode k) = chartA k ∧
      discA (antipode k) = discB k ∧ discB (antipode k) = discA k := by
  decide

/-- 4c. ...and magenta swaps Truth with Discovery inside each body. -/
theorem magenta_swaps_within_each_body :
    ∀ k : Seat, chartA (magenta k) = discA k ∧ discA (magenta k) = chartA k ∧
      chartB (magenta k) = discB k ∧ discB (magenta k) = chartB k := by
  decide

theorem where_forgery_shows_certificate :
    (∀ k : Seat, ¬ Genuine (relabel (truthFromA k)) ↔ k.val % 3 = 1) ∧
    (∀ k : Seat, k.val % 3 ≠ 1 → Genuine (relabel (truthFromA k))) ∧
    (∀ k : Seat, odd (antipode k) = odd k) ∧
    (∀ k : Seat, chartA (antipode k) = chartB k ∧ chartB (antipode k) = chartA k ∧
      discA (antipode k) = discB k ∧ discB (antipode k) = discA k) ∧
    (∀ k : Seat, chartA (magenta k) = discA k ∧ discA (magenta k) = chartA k ∧
      chartB (magenta k) = discB k ∧ discB (magenta k) = chartB k) :=
  ⟨forgery_caught_exactly_on_the_weld_square, forgery_passes_off_the_weld_square,
   antipode_keeps_parity, body_change_swaps_the_charts, magenta_swaps_within_each_body⟩

#print axioms forgery_caught_exactly_on_the_weld_square
#print axioms the_weld_square_is_B1_B4_B7_B10
#print axioms forgery_passes_off_the_weld_square
#print axioms antipode_keeps_parity
#print axioms still_readings_never_catch_forgery
#print axioms four_different_charts
#print axioms body_change_swaps_the_charts
#print axioms magenta_swaps_within_each_body
#print axioms where_forgery_shows_certificate

end WhereForgeryShows
