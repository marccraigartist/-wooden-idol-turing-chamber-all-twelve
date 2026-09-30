/-!
# THE MISSING BIT — FOUNDATION STONE TEST 16A: THE REPLAY BOUNDARY

Runs in the Lean live editor with no imports (core Lean only).

This test begins at 15Y–15G's blind point.  Two native 30° journeys have:

* the same start;
* different middle states;
* the same finish;
* nonzero, opposite signed bends.

The question is not whether a clever endpoint reader can usually guess the route.  It is
whether ANY deterministic computation receiving only the common endpoint can distinguish
these two particular histories or reconstruct both of their middle states.

Lean certifies:

1. NATIVE PAIR.  The two journeys finish together but have different middles and opposite
   signed bends.
2. REPLAY BOUNDARY.  Every endpoint-only observer gives the same answer on the two journeys.
   This remains true after arbitrarily many deterministic rounds of further processing.
3. NO RECONSTRUCTION.  No function of the endpoint can correctly reconstruct both middle
   states.  The endpoint projection is therefore not injective on these native histories.
4. RED CONTROL.  A provenance-bearing observer that receives the middle state separates
   the journeys, and the signed bend tells their orientation apart exactly.
5. FORGETTING LOCATION.  The information loss is located at the endpoint projection:
   forgetting provenance identifies histories that the retained histories distinguish.

This is a theorem about information loss, not unpredictability.  Both journeys are exactly
computable.  It does not say that every compressed replay is inadequate, only that no replay
factoring through THIS endpoint-only projection can recover the missing distinction.
-/
namespace FoundationStoneSixteenA

/-! ## Exact geometry over Z[sqrt 3] -/

/-- `a + b * sqrt 3`. -/
structure Z3 where
  a : Int
  b : Int
deriving DecidableEq

/-- A point with coordinates in `Z[sqrt 3]`. -/
structure V3 where
  x : Z3
  y : Z3
  z : Z3
deriving DecidableEq

def zadd (u v : Z3) : Z3 := ⟨u.a + v.a, u.b + v.b⟩
def zneg (u : Z3) : Z3 := ⟨-u.a, -u.b⟩
def zsub (u v : Z3) : Z3 := zadd u (zneg v)
def zscale (k : Int) (u : Z3) : Z3 := ⟨k * u.a, k * u.b⟩
def zroot (u : Z3) : Z3 := ⟨3 * u.b, u.a⟩
def zmul (u v : Z3) : Z3 :=
  ⟨u.a * v.a + 3 * u.b * v.b, u.a * v.b + u.b * v.a⟩

def vneg (v : V3) : V3 := ⟨zneg v.x, zneg v.y, zneg v.z⟩

/-- Twice a positive 30-degree turn about z. -/
def rzP (v : V3) : V3 :=
  ⟨zsub (zroot v.x) v.y, zadd v.x (zroot v.y), zscale 2 v.z⟩

/-- Twice a positive 30-degree turn about y. -/
def ryP (v : V3) : V3 :=
  ⟨zadd (zroot v.x) v.z, zscale 2 v.y, zadd (zneg v.x) (zroot v.z)⟩

/-- Z first, then Y; scaled by four. -/
def A (v : V3) : V3 := ryP (rzP v)

/-- Y first, then Z; scaled by four. -/
def B (v : V3) : V3 := rzP (ryP v)

/-- Triple product `u dot (v cross w)`. -/
def det3 (u v w : V3) : Z3 :=
  zadd (zadd (zmul u.x (zsub (zmul v.y w.z) (zmul v.z w.y)))
             (zmul u.y (zsub (zmul v.z w.x) (zmul v.x w.z))))
       (zmul u.z (zsub (zmul v.x w.y) (zmul v.y w.x)))

/-! ## The two native histories -/

/-- A complete two-leg journey.  The stored middle is its minimal route provenance. -/
structure Journey where
  start : V3
  middle : V3
  finish : V3
deriving DecidableEq

/-- The 15Y blind point `(1, sqrt 3 - 2, 2 - sqrt 3)`. -/
def blindPoint : V3 := ⟨⟨1, 0⟩, ⟨-2, 1⟩, ⟨2, -1⟩⟩

def journeyA : Journey := ⟨blindPoint, rzP blindPoint, A blindPoint⟩
def journeyB : Journey := ⟨blindPoint, ryP blindPoint, B blindPoint⟩

def Journey.bend (j : Journey) : Z3 := det3 j.start j.middle j.finish

/-- 1a. The two orders reach exactly the same endpoint. -/
theorem same_finish : journeyA.finish = journeyB.finish := by decide

/-- 1b. But their intermediate states differ. -/
theorem different_middles : journeyA.middle ≠ journeyB.middle := by decide

/-- 1c. Their retained signed bends are nonzero and exactly opposite. -/
theorem opposite_native_bends :
    journeyA.bend = ⟨-224, 128⟩ ∧ journeyB.bend = ⟨224, -128⟩ ∧
      journeyA.bend = zneg journeyB.bend := by
  decide

/-! ## Endpoint-only replay -/

/-- Forget the journey and retain only its completed answer. -/
def endpointOnly (j : Journey) : V3 := j.finish

/-- 2a. EVERY endpoint-only observer is blind to this pair. -/
theorem every_endpoint_observer_is_blind {R : Type} (observe : V3 → R) :
    observe (endpointOnly journeyA) = observe (endpointOnly journeyB) := by
  rw [endpointOnly, endpointOnly, same_finish]

def iter {R : Type} (step : R → R) : Nat → R → R
  | 0, r => r
  | n + 1, r => step (iter step n r)

/-- 2b. Recursively processing the endpoint cannot restore what the projection erased. -/
theorem recursive_endpoint_replay_is_blind {R : Type} (encode : V3 → R)
    (step : R → R) (n : Nat) :
    iter step n (encode (endpointOnly journeyA)) =
      iter step n (encode (endpointOnly journeyB)) := by
  rw [every_endpoint_observer_is_blind encode]

/-- The conclusion also holds if a final reader is applied after the recursive replay. -/
theorem every_postprocessed_replay_is_blind {R S : Type} (encode : V3 → R)
    (step : R → R) (read : R → S) (n : Nat) :
    read (iter step n (encode (endpointOnly journeyA))) =
      read (iter step n (encode (endpointOnly journeyB))) := by
  rw [recursive_endpoint_replay_is_blind encode step n]

/-! ## No endpoint-only route reconstruction -/

/-- 3a. No endpoint-only function can reconstruct the correct middle for both histories. -/
theorem no_endpoint_reconstructor (recover : V3 → V3) :
    ¬ (recover (endpointOnly journeyA) = journeyA.middle ∧
       recover (endpointOnly journeyB) = journeyB.middle) := by
  intro h
  have hr := congrArg recover same_finish
  have hm : journeyA.middle = journeyB.middle := h.1.symm.trans (hr.trans h.2)
  exact different_middles hm

/-- 3b. Equivalently, endpoint forgetting is not injective on the native histories. -/
theorem endpoint_projection_is_not_injective : ¬ Function.Injective endpointOnly := by
  intro hinj
  have hj : journeyA = journeyB := hinj same_finish
  exact different_middles (congrArg Journey.middle hj)

/-! ## Red controls: retained provenance really can distinguish the pair -/

/-- 4a. The provenance-bearing histories are different. -/
theorem retained_histories_are_different : journeyA ≠ journeyB := by decide

/-- 4b. Reading the middle separates them. -/
theorem middle_provenance_separates :
    journeyA.middle ≠ journeyB.middle := different_middles

/-- 4c. Reading signed bend separates their orientations. -/
theorem signed_bend_separates :
    journeyA.bend ≠ journeyB.bend := by decide

/-- 4d. If sign is forgotten by squaring, the distinction disappears again. -/
theorem squaring_bend_forgets_orientation :
    zmul journeyA.bend journeyA.bend = zmul journeyB.bend journeyB.bend := by decide

/-! ## Certificate -/

theorem replay_boundary_certificate :
    journeyA.finish = journeyB.finish ∧
    journeyA.middle ≠ journeyB.middle ∧
    journeyA.bend = zneg journeyB.bend ∧
    (∀ (R : Type) (observe : V3 → R),
      observe (endpointOnly journeyA) = observe (endpointOnly journeyB)) ∧
    (∀ recover : V3 → V3,
      ¬ (recover (endpointOnly journeyA) = journeyA.middle ∧
         recover (endpointOnly journeyB) = journeyB.middle)) ∧
    ¬ Function.Injective endpointOnly ∧
    journeyA ≠ journeyB ∧
    zmul journeyA.bend journeyA.bend = zmul journeyB.bend journeyB.bend :=
  ⟨same_finish, different_middles, opposite_native_bends.2.2,
   fun _ observe => every_endpoint_observer_is_blind observe,
   no_endpoint_reconstructor, endpoint_projection_is_not_injective,
   retained_histories_are_different, squaring_bend_forgets_orientation⟩

#print axioms same_finish
#print axioms different_middles
#print axioms opposite_native_bends
#print axioms every_endpoint_observer_is_blind
#print axioms recursive_endpoint_replay_is_blind
#print axioms every_postprocessed_replay_is_blind
#print axioms no_endpoint_reconstructor
#print axioms endpoint_projection_is_not_injective
#print axioms retained_histories_are_different
#print axioms signed_bend_separates
#print axioms squaring_bend_forgets_orientation
#print axioms replay_boundary_certificate

end FoundationStoneSixteenA
