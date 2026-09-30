/-!
# EARNED FRAME GENESIS — FOUNDATION STONE TEST 16H

Runs in the Lean live editor with no imports (core Lean only).

Test 16G proved that every finite replay prefix can be escaped by its next depth,
while a live computable process can still answer.  Test 16H asks the stronger B6
question: can an encounter FORCE a new frame, rather than merely supply another
answer inside the old one?

A history is an unbounded binary route.  Frame K can inspect exactly the first K
route decisions.  The canonical encounter agrees through every coordinate visible
to Frame K and differs at the first invisible coordinate K.

Lean certifies:
1. Frame K identifies the two histories.
2. The receiver's challenge at coordinate K separates them.
3. Frame K+1 is strictly finer than Frame K: it preserves every distinction K can
   make and makes a distinction K cannot.
4. K+1 is the LEAST frame that can distinguish this encounter.  The successor is
   therefore selected by the failure certificate, not installed as an arbitrary
   second frame.
5. Every bounded frame has such an encounter, so no member of this bounded family
   is final.
6. RED CONTROL.  The unbounded raw-history frame distinguishes the pair already.
   Hence frame genesis is earned only relative to the explicitly bounded frame
   class.  This is not absolute novelty, undecidability, or unpredictability.

This is a strengthened B6 pattern.  The original formal B6 merely asks for some
different `phi'`.  Here the encounter witnesses a strict behavioural refinement
and determines its least depth.
-/
namespace EarnedFrameGenesis

/-- A route with one binary decision available at every natural coordinate. -/
abbrev History := Nat → Bool

/-- Frame K sees precisely the coordinates below K. -/
def observe (K : Nat) (h : History) : Fin K → Bool := fun i => h i.val

/-- The left route is constantly false. -/
def leftHistory (_K : Nat) : History := fun _ => false

/-- The right route first differs at coordinate K. -/
def rightHistory (K : Nat) : History := fun n => if n = K then true else false

/-- 1. The current frame collapses the two histories. -/
theorem current_frame_is_blind (K : Nat) :
    observe K (leftHistory K) = observe K (rightHistory K) := by
  funext i
  have hne : i.val ≠ K := Nat.ne_of_lt i.isLt
  simp [observe, leftHistory, rightHistory, hne]

/-- Ask one route for the decision at coordinate n. -/
def probe (n : Nat) (h : History) : Bool := h n

/-- 2. The post-frame challenge at the first invisible coordinate separates them. -/
theorem challenge_exposes_the_difference (K : Nat) :
    probe K (leftHistory K) ≠ probe K (rightHistory K) := by
  simp [probe, leftHistory, rightHistory]

/-- Consequently the histories themselves were different all along. -/
theorem histories_are_different (K : Nat) : leftHistory K ≠ rightHistory K := by
  intro h
  exact challenge_exposes_the_difference K (congrFun h K)

/-- The successor frame can see the challenged coordinate. -/
theorem successor_frame_separates (K : Nat) :
    observe (K + 1) (leftHistory K) ≠ observe (K + 1) (rightHistory K) := by
  intro h
  have hk := congrFun h (⟨K, by omega⟩ : Fin (K + 1))
  simp [observe, leftHistory, rightHistory] at hk

/-! ## Behavioural refinement of frames -/

/-- `new` refines `old` when equality under the new observation always implies
equality under the old observation. -/
def Refines (new old : Nat) : Prop :=
  ∀ u v : History, observe new u = observe new v → observe old u = observe old v

/-- Strict refinement also requires a pair the old frame identifies and the new
frame separates. -/
def StrictlyFiner (new old : Nat) : Prop := Refines new old ∧ ¬ Refines old new

/-- 3a. Seeing K+1 decisions preserves everything visible at K. -/
theorem successor_refines_current (K : Nat) : Refines (K + 1) K := by
  intro u v h
  funext i
  have hi : i.val < K + 1 := Nat.lt_trans i.isLt (Nat.lt_succ_self K)
  exact congrFun h (⟨i.val, hi⟩ : Fin (K + 1))

/-- 3b. The reverse refinement fails on the certified encounter. -/
theorem current_does_not_refine_successor (K : Nat) : ¬ Refines K (K + 1) := by
  intro h
  exact successor_frame_separates K
    (h (leftHistory K) (rightHistory K) (current_frame_is_blind K))

/-- 3c. The encounter therefore earns a genuinely stricter frame. -/
theorem successor_is_strictly_finer (K : Nat) : StrictlyFiner (K + 1) K :=
  ⟨successor_refines_current K, current_does_not_refine_successor K⟩

/-! ## The successor is forced, not merely available -/

/-- Every frame of depth at most K remains blind to the same encounter. -/
theorem every_lower_frame_is_blind (K j : Nat) (hj : j ≤ K) :
    observe j (leftHistory K) = observe j (rightHistory K) := by
  funext i
  have hlt : i.val < K := Nat.lt_of_lt_of_le i.isLt hj
  have hne : i.val ≠ K := Nat.ne_of_lt hlt
  simp [observe, leftHistory, rightHistory, hne]

/-- 4. Any frame that distinguishes the encounter must have depth at least K+1. -/
theorem successor_is_least_separating (K j : Nat)
    (hsep : observe j (leftHistory K) ≠ observe j (rightHistory K)) : K + 1 ≤ j := by
  by_cases h : K + 1 ≤ j
  · exact h
  · have hj : j ≤ K := by omega
    exact False.elim (hsep (every_lower_frame_is_blind K j hj))

/-- The frame generated by the failed observation and its challenge. -/
def generatedFrame (K : Nat) : Nat := K + 1

/-- Thick B6: not just another frame, but the least strictly finer frame selected
by this encounter. -/
def EarnedB6At (K : Nat) : Prop :=
  ∃ φ', φ' ≠ K ∧ StrictlyFiner φ' K ∧
    observe φ' (leftHistory K) ≠ observe φ' (rightHistory K) ∧
    ∀ j, observe j (leftHistory K) ≠ observe j (rightHistory K) → φ' ≤ j

/-- 5a. Every bounded frame earns its canonical successor. -/
theorem earned_B6 (K : Nat) : EarnedB6At K := by
  refine ⟨generatedFrame K, ?_, ?_, ?_, ?_⟩
  · unfold generatedFrame
    omega
  · exact successor_is_strictly_finer K
  · exact successor_frame_separates K
  · exact successor_is_least_separating K

/-- 5b. No bounded observation depth is a final frame in this family. -/
theorem no_bounded_frame_is_final : ∀ K, ∃ φ', StrictlyFiner φ' K := by
  intro K
  exact ⟨K + 1, successor_is_strictly_finer K⟩

/-! ## Red controls and scope locks -/

/-- The unbounded frame retains the complete history. -/
def rawObserve (h : History) : History := h

/-- 6a. The raw frame already sees the distinction: boundedness is essential. -/
theorem raw_frame_needs_no_successor_for_this_encounter (K : Nat) :
    rawObserve (leftHistory K) ≠ rawObserve (rightHistory K) :=
  histories_are_different K

/-- 6b. The generated frame remains a computable function of K.  Being forced by
the encounter is not the same as being unpredictable. -/
theorem generated_frame_is_predictable (K : Nat) : generatedFrame K = K + 1 := rfl

/-- 6c. Observational separation alone asserts no historical occurrence.  Either
Boolean occurrence label is compatible with the same mathematical encounter. -/
structure Report where
  frame : Nat
  occurred : Bool

def report (K : Nat) (occurred : Bool) : Report := ⟨generatedFrame K, occurred⟩

theorem same_frame_opposite_occurrence (K : Nat) :
    (report K false).frame = (report K true).frame ∧
    (report K false).occurred ≠ (report K true).occurred := by
  refine ⟨rfl, ?_⟩
  intro h
  exact Bool.noConfusion h

/-- The complete 16H certificate. -/
theorem earned_frame_genesis_certificate :
    (∀ K, observe K (leftHistory K) = observe K (rightHistory K)) ∧
    (∀ K, probe K (leftHistory K) ≠ probe K (rightHistory K)) ∧
    (∀ K, StrictlyFiner (K + 1) K) ∧
    (∀ K j, observe j (leftHistory K) ≠ observe j (rightHistory K) → K + 1 ≤ j) ∧
    (∀ K, EarnedB6At K) ∧
    (∀ K, rawObserve (leftHistory K) ≠ rawObserve (rightHistory K)) ∧
    (∀ K, (report K false).frame = (report K true).frame ∧
      (report K false).occurred ≠ (report K true).occurred) :=
  ⟨current_frame_is_blind,
   challenge_exposes_the_difference,
   successor_is_strictly_finer,
   successor_is_least_separating,
   earned_B6,
   raw_frame_needs_no_successor_for_this_encounter,
   same_frame_opposite_occurrence⟩

#print axioms current_frame_is_blind
#print axioms challenge_exposes_the_difference
#print axioms histories_are_different
#print axioms successor_frame_separates
#print axioms successor_refines_current
#print axioms current_does_not_refine_successor
#print axioms successor_is_strictly_finer
#print axioms every_lower_frame_is_blind
#print axioms successor_is_least_separating
#print axioms earned_B6
#print axioms no_bounded_frame_is_final
#print axioms raw_frame_needs_no_successor_for_this_encounter
#print axioms generated_frame_is_predictable
#print axioms same_frame_opposite_occurrence
#print axioms earned_frame_genesis_certificate

end EarnedFrameGenesis
