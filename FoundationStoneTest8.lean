import Mathlib

/-!
# THE FOUNDATION STONE — TEST 8: CAN THE RELAY CREATE DIRECTION?

Test 7 proved that shared direction, reciprocity and separation force an arbitrary
two-body transport to be the six-seat antipode.  Test 8 asks whether an otherwise
orientation-free relay can create that shared direction.

Lean checks two complementary results.

RED — no direction from a perfectly symmetric beginning:
1. The undirected clock remembers adjacency but forgets clockwise versus anticlockwise.
2. Both the antipode and the magenta reflection preserve that adjacency, are reciprocal,
   and have no fixed seat.
3. They are different maps.  Therefore the undirected requirements do not determine a
   unique transport.
4. More generally, no reflection-equivariant deterministic chooser can select one of two
   opposite directions from a reflection-fixed transcript.

GREEN — one ordered event is sufficient:
5. An ordered adjacent pair is the finite "pebble": it distinguishes clockwise from
   anticlockwise, and reflection reverses its answer.
6. A transport respecting the direction named by that pebble is forced to be a rotation.
7. Adding reciprocity and separation forces that rotation to be the six-seat antipode.
   Hence B's B1 is A's B7.

Honest result: the neutral relay can preserve and transmit an orientation, but cannot
choose one without breaking reflection symmetry.  The ordered pebble is not derived from
the symmetric clock; it is the minimal asymmetric input in this model.

This is a finite symmetry-breaking and rigidity result.  It is not a P-versus-NP result,
an incompleteness theorem, or evidence that physical systems must behave this way.
-/

namespace FoundationStoneTestEight

abbrev Seat := Fin 12

def clockForward (seat : Seat) : Seat := seat + 1
def clockBack (seat : Seat) : Seat := seat + 11
def rotation (offset seat : Seat) : Seat := seat + offset
def antipode (seat : Seat) : Seat := seat + 6
def magenta (seat : Seat) : Seat := 11 - seat

/-- The clock with orientation forgotten. -/
def Adjacent (a b : Seat) : Prop := b = clockForward a ∨ b = clockBack a

def PreservesAdjacency (f : Seat → Seat) : Prop :=
  ∀ a b, Adjacent a b ↔ Adjacent (f a) (f b)

def Reciprocal (f : Seat → Seat) : Prop := ∀ seat, f (f seat) = seat
def Separate (f : Seat → Seat) : Prop := ∀ seat, f seat ≠ seat

/-- Everything visible to an undirected two-body relay. -/
def UndirectedAdmissible (f : Seat → Seat) : Prop :=
  PreservesAdjacency f ∧ Reciprocal f ∧ Separate f

theorem antipode_reciprocal : Reciprocal antipode := by
  intro seat
  fin_cases seat <;> decide

theorem antipode_separate : Separate antipode := by
  intro seat
  fin_cases seat <;> decide

theorem magenta_reciprocal : Reciprocal magenta := by
  intro seat
  fin_cases seat <;> decide

theorem magenta_separate : Separate magenta := by
  intro seat
  fin_cases seat <;> decide

theorem reciprocal_mapping_preserves_adjacency (f : Seat → Seat)
    (hreciprocal : Reciprocal f)
    (hmaps : ∀ a b, Adjacent a b → Adjacent (f a) (f b)) :
    PreservesAdjacency f := by
  intro a b
  constructor
  · exact hmaps a b
  · intro h
    have hh := hmaps (f a) (f b) h
    simpa [hreciprocal a, hreciprocal b] using hh

theorem antipode_maps_adjacency :
    ∀ a b, Adjacent a b → Adjacent (antipode a) (antipode b) := by
  intro a b h
  rcases h with h | h
  · left
    rw [h]
    change (a + 1) + 6 = (a + 6) + 1
    abel
  · right
    rw [h]
    change (a + 11) + 6 = (a + 6) + 11
    abel

theorem antipode_preserves_adjacency : PreservesAdjacency antipode :=
  reciprocal_mapping_preserves_adjacency
    antipode antipode_reciprocal antipode_maps_adjacency

theorem magenta_forward_to_back : ∀ seat,
    magenta (clockForward seat) = clockBack (magenta seat) := by
  intro seat
  fin_cases seat <;> decide

theorem magenta_back_to_forward : ∀ seat,
    magenta (clockBack seat) = clockForward (magenta seat) := by
  intro seat
  fin_cases seat <;> decide

theorem magenta_maps_adjacency :
    ∀ a b, Adjacent a b → Adjacent (magenta a) (magenta b) := by
  intro a b h
  rcases h with h | h
  · right
    rw [h]
    exact magenta_forward_to_back a
  · left
    rw [h]
    exact magenta_back_to_forward a

theorem magenta_preserves_adjacency : PreservesAdjacency magenta :=
  reciprocal_mapping_preserves_adjacency
    magenta magenta_reciprocal magenta_maps_adjacency

theorem antipode_admissible : UndirectedAdmissible antipode :=
  ⟨antipode_preserves_adjacency, antipode_reciprocal, antipode_separate⟩

theorem magenta_admissible : UndirectedAdmissible magenta :=
  ⟨magenta_preserves_adjacency, magenta_reciprocal, magenta_separate⟩

theorem antipode_ne_magenta : antipode ≠ magenta := by
  intro h
  have h0 := congrFun h (0 : Seat)
  exact (by decide : antipode (0 : Seat) ≠ magenta (0 : Seat)) h0

/-- RED 1: the complete orientation-free specification admits two different transports. -/
theorem undirected_has_two_transports :
    ∃ f g : Seat → Seat,
      UndirectedAdmissible f ∧ UndirectedAdmissible g ∧ f ≠ g :=
  ⟨antipode, magenta, antipode_admissible, magenta_admissible, antipode_ne_magenta⟩

/-- RED 2: consequently, the undirected specification cannot define one unique relay. -/
theorem undirected_no_unique_transport : ¬ ∃! f : Seat → Seat, UndirectedAdmissible f := by
  intro h
  obtain ⟨f, hf, hunique⟩ := h
  have ha : antipode = f := hunique antipode antipode_admissible
  have hm : magenta = f := hunique magenta magenta_admissible
  exact antipode_ne_magenta (ha.trans hm.symm)

/-! ## The abstract symmetry obstruction -/

inductive Direction
  | clockwise
  | anticlockwise
deriving DecidableEq

def opposite : Direction → Direction
  | .clockwise => .anticlockwise
  | .anticlockwise => .clockwise

theorem opposite_ne_self : ∀ d : Direction, opposite d ≠ d := by
  intro d
  cases d <;> decide

/-- A chooser respects reflection when reflecting its input reverses its answer. -/
def ReflectionEquivariant {View : Type} (reflect : View → View)
    (choose : View → Direction) : Prop :=
  ∀ view, choose (reflect view) = opposite (choose view)

/-- RED 3: a reflection-fixed view cannot yield a deterministic orientation without
breaking its symmetry. -/
theorem symmetric_view_cannot_choose {View : Type} (reflect : View → View)
    (view : View) (hsymmetric : reflect view = view) :
    ¬ ∃ choose : View → Direction, ReflectionEquivariant reflect choose := by
  rintro ⟨choose, hequivariant⟩
  have h := hequivariant view
  rw [hsymmetric] at h
  exact opposite_ne_self (choose view) h.symm

/-- A concrete neutral transcript carries counts but no orientation labels.  Reflection
therefore changes nothing. -/
structure NeutralTranscript where
  pulses : List Nat

def reflectNeutral (t : NeutralTranscript) : NeutralTranscript := t

theorem neutral_transcript_cannot_choose (t : NeutralTranscript) :
    ¬ ∃ choose : NeutralTranscript → Direction,
      ReflectionEquivariant reflectNeutral choose :=
  symmetric_view_cannot_choose reflectNeutral t rfl

/-! ## The ordered pebble -/

/-- Read an ordered pair as clockwise when its second seat is one step forward; otherwise
read it as anticlockwise.  `OrientedPebble` below ensures the pair really is adjacent. -/
def orderedDirection (a b : Seat) : Direction :=
  if b = clockForward a then .clockwise else .anticlockwise

structure OrientedPebble where
  origin : Seat
  destination : Seat
  adjacent : Adjacent origin destination

def pebbleDirection (p : OrientedPebble) : Direction :=
  orderedDirection p.origin p.destination

theorem forward_ne_back : ∀ seat : Seat, clockForward seat ≠ clockBack seat := by
  intro seat
  fin_cases seat <;> decide

theorem forward_pebble_reads_clockwise (origin : Seat) :
    orderedDirection origin (clockForward origin) = .clockwise := by
  simp [orderedDirection]

theorem backward_pebble_reads_anticlockwise (origin : Seat) :
    orderedDirection origin (clockBack origin) = .anticlockwise := by
  simp [orderedDirection, (forward_ne_back origin).symm]

/-- Reflection turns the ordered pebble around. -/
theorem magenta_reverses_ordered_direction (a b : Seat) (h : Adjacent a b) :
    orderedDirection (magenta a) (magenta b) = opposite (orderedDirection a b) := by
  rcases h with h | h
  · rw [h, magenta_forward_to_back]
    simp [orderedDirection, opposite, (forward_ne_back (magenta a)).symm]
  · rw [h, magenta_back_to_forward]
    simp [orderedDirection, opposite, (forward_ne_back a).symm]

def reflectPebble (p : OrientedPebble) : OrientedPebble where
  origin := magenta p.origin
  destination := magenta p.destination
  adjacent := (magenta_preserves_adjacency p.origin p.destination).mp p.adjacent

theorem reflected_pebble_reverses_direction (p : OrientedPebble) :
    pebbleDirection (reflectPebble p) = opposite (pebbleDirection p) :=
  magenta_reverses_ordered_direction p.origin p.destination p.adjacent

/-! ## From the pebble to the Stage 7 rigidity result -/

def step : Direction → Seat → Seat
  | .clockwise => clockForward
  | .anticlockwise => clockBack

def SharesDirection (d : Direction) (f : Seat → Seat) : Prop :=
  ∀ seat, f (step d seat) = step d (f seat)

def SharesForward (f : Seat → Seat) : Prop := SharesDirection .clockwise f

def iterF (f : Seat → Seat) : Nat → Seat → Seat
  | 0, seat => seat
  | n + 1, seat => f (iterF f n seat)

theorem shares_iter (f move : Seat → Seat)
    (h : ∀ seat, f (move seat) = move (f seat)) :
    ∀ n seat, f (iterF move n seat) = iterF move n (f seat) := by
  intro n
  induction n with
  | zero => intro seat; rfl
  | succ n ih =>
      intro seat
      simp only [iterF]
      rw [h, ih]

theorem eleven_back_is_forward : ∀ seat : Seat,
    iterF clockBack 11 seat = clockForward seat := by
  intro seat
  fin_cases seat <;> decide

/-- Commuting with the reverse step also implies commuting with the forward step, because
eleven reverse steps equal one forward step on the twelve-seat clock. -/
theorem shares_back_implies_forward (f : Seat → Seat)
    (h : SharesDirection .anticlockwise f) : SharesForward f := by
  intro seat
  have hi := shares_iter f clockBack h 11 seat
  rw [eleven_back_is_forward seat] at hi
  rw [eleven_back_is_forward (f seat)] at hi
  exact hi

theorem shares_selected_direction_implies_forward (d : Direction) (f : Seat → Seat)
    (h : SharesDirection d f) : SharesForward f := by
  cases d with
  | clockwise => exact h
  | anticlockwise => exact shares_back_implies_forward f h

theorem seat_generated_from_zero : ∀ seat : Seat,
    iterF clockForward seat.val (0 : Seat) = seat := by
  intro seat
  fin_cases seat <;> decide

theorem iter_forward_from_seat : ∀ target start : Seat,
    iterF clockForward target.val start = rotation start target := by
  intro target start
  fin_cases target <;>
    simp [iterF, clockForward, rotation, add_comm, add_left_comm]

theorem shared_forward_forces_rotation (f : Seat → Seat) (h : SharesForward f) :
    ∀ seat, f seat = rotation (f 0) seat := by
  intro seat
  have heq := shares_iter f clockForward h seat.val (0 : Seat)
  rw [seat_generated_from_zero seat] at heq
  rw [iter_forward_from_seat seat (f 0)] at heq
  exact heq

theorem reciprocal_rotation_iff_double_zero (offset : Seat) :
    Reciprocal (rotation offset) ↔ offset + offset = 0 := by
  constructor
  · intro h
    simpa [Reciprocal, rotation] using h (0 : Seat)
  · intro h seat
    unfold rotation
    rw [add_assoc, h, add_zero]

theorem reciprocal_rotation_offset (offset : Seat)
    (h : Reciprocal (rotation offset)) : offset = 0 ∨ offset = 6 := by
  have hdbl := (reciprocal_rotation_iff_double_zero offset).mp h
  fin_cases offset <;> simp_all

theorem separate_rotation_nonzero (offset : Seat)
    (h : Separate (rotation offset)) : offset ≠ 0 := by
  intro hoffset
  subst hoffset
  exact h 0 (by decide)

theorem selected_direction_reciprocal_separation_forces_antipode
    (d : Direction) (f : Seat → Seat)
    (hshared : SharesDirection d f) (hreciprocal : Reciprocal f)
    (hseparate : Separate f) : ∀ seat, f seat = antipode seat := by
  have hforward := shares_selected_direction_implies_forward d f hshared
  have hform := shared_forward_forces_rotation f hforward
  have hrecrot : Reciprocal (rotation (f 0)) := by
    intro seat
    rw [← hform seat, ← hform (f seat)]
    exact hreciprocal seat
  have hseprot : Separate (rotation (f 0)) := by
    intro seat
    rw [← hform seat]
    exact hseparate seat
  have hsix : f 0 = 6 := by
    rcases reciprocal_rotation_offset (f 0) hrecrot with hzero | hsix
    · exact False.elim (separate_rotation_nonzero (f 0) hseprot hzero)
    · exact hsix
  intro seat
  rw [hform seat, hsix]
  rfl

/-- GREEN: the ordered pebble supplies exactly the orientation that the neutral relay
could not manufacture.  Respecting it globally, together with reciprocity and separation,
forces the antipodal two-body alignment. -/
theorem pebble_relay_forces_antipode (p : OrientedPebble) (f : Seat → Seat)
    (hshared : SharesDirection (pebbleDirection p) f)
    (hreciprocal : Reciprocal f) (hseparate : Separate f) :
    ∀ seat, f seat = antipode seat :=
  selected_direction_reciprocal_separation_forces_antipode
    (pebbleDirection p) f hshared hreciprocal hseparate

/-- In the resulting alignment, B's B1 is A's B7. -/
theorem pebble_relay_B1_is_B7 (p : OrientedPebble) (f : Seat → Seat)
    (hshared : SharesDirection (pebbleDirection p) f)
    (hreciprocal : Reciprocal f) (hseparate : Separate f) : f 1 = 7 := by
  rw [pebble_relay_forces_antipode p f hshared hreciprocal hseparate]
  decide

/-! ## Complete certificate -/

theorem foundation_stone_test_eight :
    (∃ f g : Seat → Seat,
      UndirectedAdmissible f ∧ UndirectedAdmissible g ∧ f ≠ g) ∧
    (¬ ∃! f : Seat → Seat, UndirectedAdmissible f) ∧
    (∀ (View : Type) (reflect : View → View) (view : View), reflect view = view →
      ¬ ∃ choose : View → Direction, ReflectionEquivariant reflect choose) ∧
    (∀ a b, Adjacent a b → orderedDirection (magenta a) (magenta b) =
      opposite (orderedDirection a b)) ∧
    (∀ (p : OrientedPebble) (f : Seat → Seat),
      SharesDirection (pebbleDirection p) f → Reciprocal f → Separate f →
        ∀ seat, f seat = antipode seat) ∧
    (∀ (p : OrientedPebble) (f : Seat → Seat),
      SharesDirection (pebbleDirection p) f → Reciprocal f → Separate f → f 1 = 7) :=
  ⟨undirected_has_two_transports,
   undirected_no_unique_transport,
   (fun View reflect view =>
      symmetric_view_cannot_choose (View := View) reflect view),
   magenta_reverses_ordered_direction,
   pebble_relay_forces_antipode,
   pebble_relay_B1_is_B7⟩

#print axioms undirected_has_two_transports
#print axioms undirected_no_unique_transport
#print axioms symmetric_view_cannot_choose
#print axioms neutral_transcript_cannot_choose
#print axioms magenta_reverses_ordered_direction
#print axioms reflected_pebble_reverses_direction
#print axioms shares_back_implies_forward
#print axioms shared_forward_forces_rotation
#print axioms selected_direction_reciprocal_separation_forces_antipode
#print axioms pebble_relay_forces_antipode
#print axioms pebble_relay_B1_is_B7
#print axioms foundation_stone_test_eight

end FoundationStoneTestEight
