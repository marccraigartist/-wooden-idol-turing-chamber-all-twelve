import Mathlib

/-!
# THE RETURN LEDGER — TEST 11: WHAT DID THE OBSERVER FORGET?

Tests 9 and 10 separated a closed circular shadow from a non-closing lifted state.
This test makes the resulting hierarchy explicit and tries to break every converse.

A complete state retains:
* a spatial state;
* helix height;
* ordered history.

An observer may successively forget history, height and spatial detail.  Lean proves
that equality descends through those projections, while explicit red controls show
that it cannot in general be reconstructed upwards.

The test also checks the dynamical source of the distinctions:
* positive rise prevents full return;
* zero rise permits return when history is also forgotten;
* commuting moves can share an endpoint while their ordered histories remain distinct;
* five-, seven- and twelve-seat shadows all close, while their positive lifts do not.

Honest scope: retained height and history are modelling choices.  This file proves
exactly what those choices imply; it does not claim that every physical observer must
retain them, nor does it establish P versus NP or undecidability.
-/

namespace FoundationStoneTestEleven

/-! ## Part 1 — four meanings of “the same” -/

structure FullState (Spatial Tag : Type) where
  spatial : Spatial
  height : Nat
  history : List Tag
deriving DecidableEq

def SameFull {Spatial Tag : Type} (a b : FullState Spatial Tag) : Prop := a = b

def SameLifted {Spatial Tag : Type} (a b : FullState Spatial Tag) : Prop :=
  a.spatial = b.spatial ∧ a.height = b.height

def SameSpatial {Spatial Tag : Type} (a b : FullState Spatial Tag) : Prop :=
  a.spatial = b.spatial

def SameShadow {Spatial Tag Shadow : Type} (project : Spatial → Shadow)
    (a b : FullState Spatial Tag) : Prop :=
  project a.spatial = project b.spatial

/-- Complete equality always implies equality after forgetting history. -/
theorem full_implies_lifted {Spatial Tag : Type} {a b : FullState Spatial Tag}
    (h : SameFull a b) : SameLifted a b := by
  subst b
  exact ⟨rfl, rfl⟩

/-- Equality after forgetting history implies equality after forgetting height. -/
theorem lifted_implies_spatial {Spatial Tag : Type} {a b : FullState Spatial Tag}
    (h : SameLifted a b) : SameSpatial a b := h.1

/-- Spatial equality implies equality of every visible projection. -/
theorem spatial_implies_shadow {Spatial Tag Shadow : Type} (project : Spatial → Shadow)
    {a b : FullState Spatial Tag} (h : SameSpatial a b) : SameShadow project a b := by
  unfold SameSpatial at h
  unfold SameShadow
  rw [h]

/-- The complete downward implication chain. -/
theorem return_descends {Spatial Tag Shadow : Type} (project : Spatial → Shadow)
    {a b : FullState Spatial Tag} (h : SameFull a b) :
    SameLifted a b ∧ SameSpatial a b ∧ SameShadow project a b := by
  have hl := full_implies_lifted h
  have hs := lifted_implies_spatial hl
  exact ⟨hl, hs, spatial_implies_shadow project hs⟩

/-! ## Part 2 — red controls: none of the converses is valid -/

inductive Tag
  | A
  | B
deriving DecidableEq

structure SpatialExample where
  place : Bool
  orientation : Bool
deriving DecidableEq

def visiblePlace (s : SpatialExample) : Bool := s.place

def shadowLeft : FullState SpatialExample Tag :=
  ⟨⟨false, false⟩, 0, []⟩

def shadowRight : FullState SpatialExample Tag :=
  ⟨⟨false, true⟩, 0, []⟩

/-- Same visible shadow does not imply the same spatial state. -/
theorem shadow_does_not_force_spatial :
    SameShadow visiblePlace shadowLeft shadowRight ∧
    ¬ SameSpatial shadowLeft shadowRight := by
  simp [SameShadow, SameSpatial, visiblePlace, shadowLeft, shadowRight]

def groundState : FullState SpatialExample Tag :=
  ⟨⟨false, false⟩, 0, []⟩

def upperState : FullState SpatialExample Tag :=
  ⟨⟨false, false⟩, 1, []⟩

/-- Same spatial state does not imply the same lifted state. -/
theorem spatial_does_not_force_lifted :
    SameSpatial groundState upperState ∧
    ¬ SameLifted groundState upperState := by
  simp [SameSpatial, SameLifted, groundState, upperState]

def routeAB : FullState SpatialExample Tag :=
  ⟨⟨false, false⟩, 2, [.A, .B]⟩

def routeBA : FullState SpatialExample Tag :=
  ⟨⟨false, false⟩, 2, [.B, .A]⟩

/-- Same lifted endpoint does not imply the same complete state or route. -/
theorem lifted_does_not_force_full :
    SameLifted routeAB routeBA ∧ ¬ SameFull routeAB routeBA := by
  simp [SameLifted, SameFull, routeAB, routeBA]

def forgetHistory {Spatial Tag : Type} (s : FullState Spatial Tag) : Spatial × Nat :=
  (s.spatial, s.height)

def forgetHeightAndHistory {Spatial Tag : Type} (s : FullState Spatial Tag) : Spatial :=
  s.spatial

/-- The history-forgetting projection really identifies different complete states. -/
theorem forgetting_history_is_not_injective :
    ¬ Function.Injective
      (@forgetHistory SpatialExample Tag) := by
  intro hinj
  have hsame : forgetHistory routeAB = forgetHistory routeBA := rfl
  exact (lifted_does_not_force_full.2) (hinj hsame)

/-- The height-forgetting projection also identifies different complete states. -/
theorem forgetting_height_is_not_injective :
    ¬ Function.Injective
      (@forgetHeightAndHistory SpatialExample Tag) := by
  intro hinj
  have hsame : forgetHeightAndHistory groundState =
      forgetHeightAndHistory upperState := rfl
  exact (by decide : groundState ≠ upperState) (hinj hsame)

/-! ## Part 3 — movement, rise and retained route -/

def step {Spatial Tag : Type} (tag : Tag) (rise : Nat) (move : Spatial → Spatial)
    (s : FullState Spatial Tag) : FullState Spatial Tag :=
  ⟨move s.spatial, s.height + rise, tag :: s.history⟩

def run {Spatial Tag : Type} (tag : Tag) (rise : Nat) (move : Spatial → Spatial) :
    Nat → FullState Spatial Tag → FullState Spatial Tag
  | 0, s => s
  | n + 1, s => step tag rise move (run tag rise move n s)

def iterF {X : Type} (f : X → X) : Nat → X → X
  | 0, x => x
  | n + 1, x => f (iterF f n x)

theorem run_projects_to_spatial {Spatial Tag : Type} (tag : Tag) (rise : Nat)
    (move : Spatial → Spatial) :
    ∀ n s, (run tag rise move n s).spatial = iterF move n s.spatial := by
  intro n
  induction n with
  | zero => intro s; rfl
  | succ n ih =>
      intro s
      simp only [run, step, iterF]
      exact congrArg move (ih s)

theorem run_height {Spatial Tag : Type} (tag : Tag) (rise : Nat)
    (move : Spatial → Spatial) :
    ∀ n s, (run tag rise move n s).height = s.height + n * rise := by
  intro n
  induction n with
  | zero => intro s; simp [run]
  | succ n ih =>
      intro s
      simp only [run, step]
      rw [ih]
      rw [Nat.succ_mul]
      omega

theorem run_history {Spatial Tag : Type} (tag : Tag) (rise : Nat)
    (move : Spatial → Spatial) :
    ∀ n s, (run tag rise move n s).history = List.replicate n tag ++ s.history := by
  intro n
  induction n with
  | zero => intro s; rfl
  | succ n ih =>
      intro s
      simp only [run, step, List.replicate_succ, ih, List.cons_append]

/-- Any positive rise over any positive run forbids complete return. -/
theorem positive_rise_prevents_full_return {Spatial Tag : Type}
    (tag : Tag) (rise : Nat) (move : Spatial → Spatial)
    (hrise : 0 < rise) (n : Nat) (hn : 0 < n) :
    ∀ s, run tag rise move n s ≠ s := by
  intro s hreturn
  have hh := congrArg FullState.height hreturn
  rw [run_height] at hh
  have hprod : 0 < n * rise := Nat.mul_pos hn hrise
  omega

/-! ## Part 4 — destructive forgetting controls -/

structure ReducedState (Spatial : Type) where
  spatial : Spatial
  height : Nat
deriving DecidableEq

def reducedStep {Spatial : Type} (rise : Nat) (move : Spatial → Spatial)
    (s : ReducedState Spatial) : ReducedState Spatial :=
  ⟨move s.spatial, s.height + rise⟩

/-- With history deleted, zero rise and an identity move really do return. -/
theorem zero_rise_identity_returns {Spatial : Type} (s : ReducedState Spatial) :
    reducedStep 0 id s = s := by
  cases s
  rfl

/-- If history remains, even a zero-rise identity move is a different full state. -/
theorem history_alone_records_passage :
    step .A 0 id groundState ≠ groundState := by decide

/-- Two commuting identity moves share endpoint and height but preserve different order. -/
theorem commuting_orders_same_endpoint_different_route :
    SameLifted (step .A 0 id (step .B 0 id groundState))
      (step .B 0 id (step .A 0 id groundState)) ∧
    ¬ SameFull (step .A 0 id (step .B 0 id groundState))
      (step .B 0 id (step .A 0 id groundState)) := by
  simp [SameLifted, SameFull, step, groundState]

/-- A one-point space collapses spatial distinction, but not height or history. -/
theorem one_point_collapses_only_space (a b : FullState Unit Tag) : SameSpatial a b := by
  unfold SameSpatial
  cases a.spatial
  cases b.spatial
  rfl

/-! ## Part 5 — N5, N7 and N12 controls -/

def finTurn {N : Nat} (k : Fin N) (x : Fin N) : Fin N := x + k

theorem five_seven_twelve_shadows_close :
    (∀ x : Fin 5, iterF (finTurn 1) 5 x = x) ∧
    (∀ x : Fin 7, iterF (finTurn 1) 7 x = x) ∧
    (∀ x : Fin 12, iterF (finTurn 1) 12 x = x) := by
  decide

def clockStart {N : Nat} [NeZero N] : FullState (Fin N) Tag :=
  ⟨0, 0, []⟩

/-- All three shadows close; all three positive lifts remain different full states. -/
theorem three_clocks_same_return_split :
    ((run Tag.A 1 (finTurn 1) 5 (clockStart (N := 5))).spatial = 0 ∧
      run Tag.A 1 (finTurn 1) 5 (clockStart (N := 5)) ≠ clockStart (N := 5)) ∧
    ((run Tag.A 1 (finTurn 1) 7 (clockStart (N := 7))).spatial = 0 ∧
      run Tag.A 1 (finTurn 1) 7 (clockStart (N := 7)) ≠ clockStart (N := 7)) ∧
    ((run Tag.A 1 (finTurn 1) 12 (clockStart (N := 12))).spatial = 0 ∧
      run Tag.A 1 (finTurn 1) 12 (clockStart (N := 12)) ≠ clockStart (N := 12)) := by
  constructor
  · constructor
    · change iterF (finTurn 1) 5 (0 : Fin 5) = 0
      exact five_seven_twelve_shadows_close.1 0
    · exact positive_rise_prevents_full_return Tag.A 1 (finTurn 1)
        (by decide) 5 (by decide) _
  · constructor
    · constructor
      · change iterF (finTurn 1) 7 (0 : Fin 7) = 0
        exact five_seven_twelve_shadows_close.2.1 0
      · exact positive_rise_prevents_full_return Tag.A 1 (finTurn 1)
          (by decide) 7 (by decide) _
    · constructor
      · change iterF (finTurn 1) 12 (0 : Fin 12) = 0
        exact five_seven_twelve_shadows_close.2.2 0
      · exact positive_rise_prevents_full_return Tag.A 1 (finTurn 1)
          (by decide) 12 (by decide) _

/-! ## Certificate -/

theorem return_ledger_certificate :
    (∀ (Spatial Tag Shadow : Type) (project : Spatial → Shadow)
      (a b : FullState Spatial Tag), SameFull a b →
        SameLifted a b ∧ SameSpatial a b ∧ SameShadow project a b) ∧
    (SameShadow visiblePlace shadowLeft shadowRight ∧
      ¬ SameSpatial shadowLeft shadowRight) ∧
    (SameSpatial groundState upperState ∧
      ¬ SameLifted groundState upperState) ∧
    (SameLifted routeAB routeBA ∧ ¬ SameFull routeAB routeBA) ∧
    (∀ (Spatial Tag : Type) (tag : Tag) (rise : Nat) (move : Spatial → Spatial),
      0 < rise → ∀ n, 0 < n → ∀ s, run tag rise move n s ≠ s) ∧
    (¬ Function.Injective (@forgetHistory SpatialExample Tag)) :=
  ⟨fun _ _ _ project _ _ h => return_descends project h,
   shadow_does_not_force_spatial,
   spatial_does_not_force_lifted,
   lifted_does_not_force_full,
   fun _ _ tag rise move hrise n hn =>
     positive_rise_prevents_full_return tag rise move hrise n hn,
   forgetting_history_is_not_injective⟩

#print axioms return_descends
#print axioms shadow_does_not_force_spatial
#print axioms spatial_does_not_force_lifted
#print axioms lifted_does_not_force_full
#print axioms forgetting_history_is_not_injective
#print axioms forgetting_height_is_not_injective
#print axioms run_projects_to_spatial
#print axioms run_height
#print axioms run_history
#print axioms positive_rise_prevents_full_return
#print axioms zero_rise_identity_returns
#print axioms history_alone_records_passage
#print axioms commuting_orders_same_endpoint_different_route
#print axioms one_point_collapses_only_space
#print axioms five_seven_twelve_shadows_close
#print axioms three_clocks_same_return_split
#print axioms return_ledger_certificate

end FoundationStoneTestEleven
