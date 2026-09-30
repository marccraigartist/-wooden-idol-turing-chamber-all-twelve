import Mathlib

/-!
# THE RETURN SIGNATURE — TEST 13: WHAT SURVIVES A CLOSED JOURNEY?

Test 11 separated four meanings of return.  Test 12 showed that the clock shadow,
the ordered spatial composite and the retained process have genuinely different
closure behaviour.  Test 13 packages those distinctions into one compositional
object.

A route is a finite list of moves.  Each move carries:
* a spatial residue in a group `G`;
* a signed height change;
* a provenance tag.

Its return signature is

    (ordered product of spatial residues,
     sum of signed height changes,
     ordered list of provenance tags).

Lean proves:
1. the empty route has the neutral signature;
2. concatenating routes multiplies/adds/appends their signatures;
3. reversing a route and inverting every move inverts the spatial residue and
   negates the height;
4. a route followed by its reverse therefore returns spatially and in height;
5. nevertheless its raw provenance is nonempty whenever the outward route was
   nonempty;
6. complete return implies lifted return, which implies shadow return;
7. explicit red controls refute both converses;
8. an order-three spatial residue closes after three moves while its positive
   height and history remain open.

The signature is not claimed to be a new invariant in abstract mathematics.
Products, cocycles and words are standard.  The result here is the exact object
needed by the Wooden Idol exploration: one ledger in which spatial closure,
helix displacement and provenance can no longer be silently substituted for one
another.

Honest scope:
* provenance is deliberately stored as a raw word; no cancellation or equivalence
  relation on histories is imposed;
* spatial return means that the accumulated group residue is the identity, a
  stronger condition than one chosen point returning under a non-faithful action;
* this is a finite compositional theorem, not undecidability or P versus NP.
-/

namespace FoundationStoneTestThirteen

/-! ## Part 1 — moves, routes and their three-coordinate signature -/

structure Move (G Tag : Type) where
  spatial : G
  rise : Int
  tag : Tag
deriving DecidableEq

abbrev Route (G Tag : Type) := List (Move G Tag)

@[ext] structure ReturnSignature (G Tag : Type) where
  spatial : G
  height : Int
  history : List Tag
deriving DecidableEq

def neutralSignature {G Tag : Type} [One G] : ReturnSignature G Tag :=
  ⟨1, 0, []⟩

def combine {G Tag : Type} [Mul G]
    (a b : ReturnSignature G Tag) : ReturnSignature G Tag :=
  ⟨a.spatial * b.spatial, a.height + b.height, a.history ++ b.history⟩

def signature {G Tag : Type} [Monoid G]
    (r : Route G Tag) : ReturnSignature G Tag :=
  ⟨(r.map Move.spatial).prod,
   (r.map Move.rise).sum,
   r.map Move.tag⟩

/-- The empty journey has done nothing at every retained level. -/
theorem signature_nil {G Tag : Type} [Monoid G] :
    signature ([] : Route G Tag) = neutralSignature := by
  rfl

/-- The central law: route concatenation is visible in all three coordinates. -/
theorem signature_append {G Tag : Type} [Monoid G]
    (p q : Route G Tag) :
    signature (p ++ q) = combine (signature p) (signature q) := by
  ext <;> simp [signature, combine]

theorem signature_spatial {G Tag : Type} [Monoid G] (r : Route G Tag) :
    (signature r).spatial = (r.map Move.spatial).prod := rfl

theorem signature_height {G Tag : Type} [Monoid G] (r : Route G Tag) :
    (signature r).height = (r.map Move.rise).sum := rfl

theorem signature_history {G Tag : Type} [Monoid G] (r : Route G Tag) :
    (signature r).history = r.map Move.tag := rfl

theorem signature_history_length {G Tag : Type} [Monoid G] (r : Route G Tag) :
    (signature r).history.length = r.length := by
  simp [signature]

/-! ## Part 2 — three return predicates and the downward implication chain -/

def ShadowReturn {G Tag : Type} [Monoid G] (r : Route G Tag) : Prop :=
  (signature r).spatial = 1

def LiftedReturn {G Tag : Type} [Monoid G] (r : Route G Tag) : Prop :=
  ShadowReturn r ∧ (signature r).height = 0

def CompleteReturn {G Tag : Type} [Monoid G] (r : Route G Tag) : Prop :=
  LiftedReturn r ∧ (signature r).history = []

theorem complete_implies_lifted {G Tag : Type} [Monoid G]
    {r : Route G Tag} (h : CompleteReturn r) : LiftedReturn r := h.1

theorem lifted_implies_shadow {G Tag : Type} [Monoid G]
    {r : Route G Tag} (h : LiftedReturn r) : ShadowReturn r := h.1

theorem complete_implies_neutral_signature {G Tag : Type} [Monoid G]
    {r : Route G Tag} (h : CompleteReturn r) :
    signature r = neutralSignature := by
  rcases h with ⟨⟨hs, hh⟩, hp⟩
  exact ReturnSignature.ext hs hh hp

theorem neutral_signature_implies_complete {G Tag : Type} [Monoid G]
    {r : Route G Tag} (h : signature r = neutralSignature) :
    CompleteReturn r := by
  unfold CompleteReturn LiftedReturn ShadowReturn
  rw [h]
  exact ⟨⟨rfl, rfl⟩, rfl⟩

theorem complete_iff_neutral_signature {G Tag : Type} [Monoid G]
    (r : Route G Tag) :
    CompleteReturn r ↔ signature r = neutralSignature :=
  ⟨complete_implies_neutral_signature,
   neutral_signature_implies_complete⟩

/-! ## Part 3 — reversing a route -/

def inverseMove {G Tag : Type} [Group G] (reverseTag : Tag → Tag)
    (m : Move G Tag) : Move G Tag :=
  ⟨m.spatial⁻¹, -m.rise, reverseTag m.tag⟩

/-- Reverse chronological order and invert every move. -/
def reverseRoute {G Tag : Type} [Group G] (reverseTag : Tag → Tag) :
    Route G Tag → Route G Tag
  | [] => []
  | m :: ms => reverseRoute reverseTag ms ++ [inverseMove reverseTag m]

theorem reverseRoute_length {G Tag : Type} [Group G] (reverseTag : Tag → Tag) :
    ∀ r : Route G Tag, (reverseRoute reverseTag r).length = r.length := by
  intro r
  induction r with
  | nil => rfl
  | cons m ms ih => simp [reverseRoute, ih]

/-- Reversal inverts the accumulated spatial residue. -/
theorem signature_reverse_spatial {G Tag : Type} [Group G]
    (reverseTag : Tag → Tag) :
    ∀ r : Route G Tag,
      (signature (reverseRoute reverseTag r)).spatial =
        (signature r).spatial⁻¹ := by
  intro r
  induction r with
  | nil => simp [reverseRoute, signature]
  | cons m ms ih =>
      rw [reverseRoute, signature_append]
      change (signature (reverseRoute reverseTag ms)).spatial *
          (signature [inverseMove reverseTag m]).spatial =
        (signature (m :: ms)).spatial⁻¹
      rw [show (signature [inverseMove reverseTag m]).spatial = m.spatial⁻¹ by
        simp [signature, inverseMove]]
      rw [show (signature (m :: ms)).spatial =
          m.spatial * (signature ms).spatial by rfl]
      rw [ih]
      exact (mul_inv_rev m.spatial (signature ms).spatial).symm

/-- Reversal negates the accumulated helix displacement. -/
theorem signature_reverse_height {G Tag : Type} [Group G]
    (reverseTag : Tag → Tag) :
    ∀ r : Route G Tag,
      (signature (reverseRoute reverseTag r)).height =
        -(signature r).height := by
  intro r
  induction r with
  | nil => simp [reverseRoute, signature]
  | cons m ms ih =>
      rw [reverseRoute, signature_append]
      change (signature (reverseRoute reverseTag ms)).height +
          (signature [inverseMove reverseTag m]).height =
        -(signature (m :: ms)).height
      rw [show (signature [inverseMove reverseTag m]).height = -m.rise by
        simp [signature, inverseMove]]
      rw [show (signature (m :: ms)).height =
          m.rise + (signature ms).height by rfl]
      rw [ih]
      omega

/-- Reversal does not erase provenance; it reverses and relabels the word. -/
theorem signature_reverse_history {G Tag : Type} [Group G]
    (reverseTag : Tag → Tag) :
    ∀ r : Route G Tag,
      (signature (reverseRoute reverseTag r)).history =
        (signature r).history.reverse.map reverseTag := by
  intro r
  induction r with
  | nil => simp [reverseRoute, signature]
  | cons m ms ih =>
      rw [reverseRoute, signature_append]
      change (signature (reverseRoute reverseTag ms)).history ++
          [reverseTag m.tag] =
        (m.tag :: (signature ms).history).reverse.map reverseTag
      rw [ih]
      simp

/-! ## Part 4 — the closed-loop theorem -/

def closedLoop {G Tag : Type} [Group G] (reverseTag : Tag → Tag)
    (r : Route G Tag) : Route G Tag :=
  r ++ reverseRoute reverseTag r

/-- Out and back has identity spatial residue. -/
theorem closed_loop_returns_spatially {G Tag : Type} [Group G]
    (reverseTag : Tag → Tag) (r : Route G Tag) :
    ShadowReturn (closedLoop reverseTag r) := by
  unfold ShadowReturn closedLoop
  rw [signature_append]
  simp only [combine, signature_reverse_spatial]
  exact mul_inv_cancel (signature r).spatial

/-- Out and back has zero signed height. -/
theorem closed_loop_returns_in_height {G Tag : Type} [Group G]
    (reverseTag : Tag → Tag) (r : Route G Tag) :
    (signature (closedLoop reverseTag r)).height = 0 := by
  unfold closedLoop
  rw [signature_append]
  simp [combine, signature_reverse_height]

theorem closed_loop_is_lifted_return {G Tag : Type} [Group G]
    (reverseTag : Tag → Tag) (r : Route G Tag) :
    LiftedReturn (closedLoop reverseTag r) :=
  ⟨closed_loop_returns_spatially reverseTag r,
   closed_loop_returns_in_height reverseTag r⟩

/-- If there was an outward journey, its out-and-back history is still nonempty. -/
theorem closed_loop_retains_provenance {G Tag : Type} [Group G]
    (reverseTag : Tag → Tag) (r : Route G Tag) (hr : r ≠ []) :
    (signature (closedLoop reverseTag r)).history ≠ [] := by
  cases r with
  | nil => exact (hr rfl).elim
  | cons m ms => simp [closedLoop, signature]

/-- Therefore a nonempty out-and-back route is closed in space and height but is
not a complete return in the provenance-retaining state. -/
theorem closed_loop_not_complete {G Tag : Type} [Group G]
    (reverseTag : Tag → Tag) (r : Route G Tag) (hr : r ≠ []) :
    LiftedReturn (closedLoop reverseTag r) ∧
      ¬ CompleteReturn (closedLoop reverseTag r) := by
  refine ⟨closed_loop_is_lifted_return reverseTag r, ?_⟩
  intro hcomplete
  exact closed_loop_retains_provenance reverseTag r hr hcomplete.2

/-! ## Part 5 — red controls for both failed converses -/

inductive Tag
  | A
  | B
deriving DecidableEq

def riseOnly : Route Unit Tag :=
  [⟨1, 1, .A⟩]

/-- Spatial identity alone does not force height to return. -/
theorem shadow_does_not_force_lifted :
    ShadowReturn riseOnly ∧ ¬ LiftedReturn riseOnly := by
  simp [ShadowReturn, LiftedReturn, signature, riseOnly]

def upThenDown : Route Unit Tag :=
  [⟨1, 1, .A⟩, ⟨1, -1, .B⟩]

/-- Space and height can return while provenance still records the passage. -/
theorem lifted_does_not_force_complete :
    LiftedReturn upThenDown ∧ ¬ CompleteReturn upThenDown := by
  simp [ShadowReturn, LiftedReturn, CompleteReturn, signature, upThenDown]

def routeAB : Route Unit Tag :=
  [⟨1, 0, .A⟩, ⟨1, 0, .B⟩]

def routeBA : Route Unit Tag :=
  [⟨1, 0, .B⟩, ⟨1, 0, .A⟩]

/-- Equal spatial residue and height do not reconstruct order. -/
theorem equal_lifted_result_different_provenance :
    (signature routeAB).spatial = (signature routeBA).spatial ∧
    (signature routeAB).height = (signature routeBA).height ∧
    signature routeAB ≠ signature routeBA := by
  decide

/-! ## Part 6 — an exact order-three return signature -/

/-- The 90° Dead Globe control has an order-three spatial residue.  We model that
residue exactly as the multiplicative form of `ZMod 3`. -/
abbrev ThreeResidue := Multiplicative (ZMod 3)

def quarterResidue : ThreeResidue := Multiplicative.ofAdd 1

def quarterMove : Move ThreeResidue Tag :=
  ⟨quarterResidue, 1, .A⟩

def threeQuarterMoves : Route ThreeResidue Tag :=
  [quarterMove, quarterMove, quarterMove]

theorem quarter_residue_has_order_three :
    quarterResidue * (quarterResidue * quarterResidue) = 1 := by
  decide

/-- Three moves close their order-three spatial residue, exactly as in Test 12,
while height and provenance prevent complete return. -/
theorem order_three_shadow_closes_process_does_not :
    ShadowReturn threeQuarterMoves ∧
    ¬ LiftedReturn threeQuarterMoves ∧
    ¬ CompleteReturn threeQuarterMoves := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [ShadowReturn, signature, threeQuarterMoves, quarterMove] using
      quarter_residue_has_order_three
  · intro h
    have hh := h.2
    norm_num [signature, threeQuarterMoves, quarterMove] at hh
  · intro h
    have hh := h.1.2
    norm_num [signature, threeQuarterMoves, quarterMove] at hh

/-! ## Certificate -/

theorem return_signature_certificate :
    (∀ (G Tag : Type) [Monoid G] (p q : Route G Tag),
      signature (p ++ q) = combine (signature p) (signature q)) ∧
    (∀ (G Tag : Type) [Group G] (reverseTag : Tag → Tag) (r : Route G Tag),
      (signature (reverseRoute reverseTag r)).spatial =
        (signature r).spatial⁻¹) ∧
    (∀ (G Tag : Type) [Group G] (reverseTag : Tag → Tag) (r : Route G Tag),
      (signature (reverseRoute reverseTag r)).height =
        -(signature r).height) ∧
    (∀ (G Tag : Type) [Group G] (reverseTag : Tag → Tag) (r : Route G Tag),
      LiftedReturn (closedLoop reverseTag r)) ∧
    (∀ (G Tag : Type) [Group G] (reverseTag : Tag → Tag) (r : Route G Tag),
      r ≠ [] → LiftedReturn (closedLoop reverseTag r) ∧
        ¬ CompleteReturn (closedLoop reverseTag r)) ∧
    (ShadowReturn riseOnly ∧ ¬ LiftedReturn riseOnly) ∧
    (LiftedReturn upThenDown ∧ ¬ CompleteReturn upThenDown) ∧
    (ShadowReturn threeQuarterMoves ∧
      ¬ LiftedReturn threeQuarterMoves ∧
      ¬ CompleteReturn threeQuarterMoves) :=
  ⟨(fun _ _ _ p q => signature_append p q),
   (fun _ _ _ reverseTag r => signature_reverse_spatial reverseTag r),
   (fun _ _ _ reverseTag r => signature_reverse_height reverseTag r),
   (fun _ _ _ reverseTag r => closed_loop_is_lifted_return reverseTag r),
   (fun _ _ _ reverseTag r hr => closed_loop_not_complete reverseTag r hr),
   shadow_does_not_force_lifted,
   lifted_does_not_force_complete,
   order_three_shadow_closes_process_does_not⟩

#print axioms signature_nil
#print axioms signature_append
#print axioms complete_iff_neutral_signature
#print axioms signature_reverse_spatial
#print axioms signature_reverse_height
#print axioms signature_reverse_history
#print axioms closed_loop_returns_spatially
#print axioms closed_loop_returns_in_height
#print axioms closed_loop_is_lifted_return
#print axioms closed_loop_retains_provenance
#print axioms closed_loop_not_complete
#print axioms shadow_does_not_force_lifted
#print axioms lifted_does_not_force_complete
#print axioms equal_lifted_result_different_provenance
#print axioms order_three_shadow_closes_process_does_not
#print axioms return_signature_certificate

end FoundationStoneTestThirteen
