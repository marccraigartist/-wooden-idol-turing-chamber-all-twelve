/-!
# THE FOUNDATION STONE — TEST 4X: THE CHART IS A COMPASS

Runs in the Lean live editor with no imports (core Lean only). Input to Test 5.

Test 4 shows that magenta gives every description a destination. That holds for any
symmetry whose vocabulary it maps to itself. This file asks which clock moves do that
for Marc's chart, and what happens under the actual TURN (magenta, then the 12–6 line:
every seat one forward).

The clock has 24 moves: 12 turns `k ↦ k + t` and 12 mirrors `k ↦ c − k`.

Order of results:
1. Only two of the 24 moves send the two-word language {Truth, Discovery} to itself:
   standing still, and magenta.
2. So the one-seat turn carries Truth OUT of that language: it lands on a chart that is
   neither Truth nor Discovery.
3. The chart has no symmetry of its own: no turn or mirror except standing still leaves
   it unchanged.
4. So its 24 images are all different, one per move. A language holding all 24 charts
   gives every move a destination, and the chart a seat lands on records EXACTLY which
   move was made. The chart is a compass: it carries the provenance of the turn.

Seat `0` is B12; seats `1`–`11` are B1–B11.
-/
namespace ChartCompass

abbrev Seat := Fin 12

/-- The truth chart {B1, B3, B4, B5, B9, B11}. -/
def truthChart (k : Seat) : Bool :=
  match k.val with
  | 1 | 3 | 4 | 5 | 9 | 11 => true
  | _ => false

/-- A move sends the two-word language to itself when the moved chart is Truth or
Discovery. -/
def KeepsTheTwoWords (g : Seat → Seat) : Prop :=
  (∀ k, truthChart (g k) = truthChart k) ∨ (∀ k, truthChart (g k) = !truthChart k)

/-- 1a. Among the turns, only standing still keeps the two words. -/
theorem turns_keeping_the_two_words :
    ∀ t : Seat, KeepsTheTwoWords (fun k => k + t) ↔ t = 0 := by
  unfold KeepsTheTwoWords
  decide

/-- 1b. Among the mirrors, only magenta keeps the two words. -/
theorem mirrors_keeping_the_two_words :
    ∀ c : Seat, KeepsTheTwoWords (fun k => c - k) ↔ c = 11 := by
  unfold KeepsTheTwoWords
  decide

/-- 2. The one-seat turn carries Truth out of the two-word language: seat by seat, the
moved chart is {B12, B2, B3, B4, B8, B10}, neither Truth nor Discovery. -/
theorem the_turn_leaves_the_two_words :
    (∀ k : Seat, truthChart (k + 1) = true ↔
      (k = 0 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 8 ∨ k = 10)) ∧
    ¬ KeepsTheTwoWords (fun k => k + 1) := by
  unfold KeepsTheTwoWords
  decide

/-- 3. The chart has no symmetry of its own. -/
theorem the_chart_has_no_symmetry :
    (∀ t : Seat, (∀ k : Seat, truthChart (k + t) = truthChart k) ↔ t = 0) ∧
    (∀ c : Seat, ¬ ∀ k : Seat, truthChart (c - k) = truthChart k) := by
  decide

/-- 4. So the 24 moved charts are all different: the chart records which move was made. -/
theorem the_chart_is_a_compass :
    (∀ t s : Seat, (∀ k : Seat, truthChart (k + t) = truthChart (k + s)) → t = s) ∧
    (∀ c d : Seat, (∀ k : Seat, truthChart (c - k) = truthChart (d - k)) → c = d) ∧
    (∀ t c : Seat, ¬ ∀ k : Seat, truthChart (k + t) = truthChart (c - k)) := by
  decide

#print axioms turns_keeping_the_two_words
#print axioms mirrors_keeping_the_two_words
#print axioms the_turn_leaves_the_two_words
#print axioms the_chart_has_no_symmetry
#print axioms the_chart_is_a_compass

end ChartCompass
