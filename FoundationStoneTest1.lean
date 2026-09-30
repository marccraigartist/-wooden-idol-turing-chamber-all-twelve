import Mathlib

/-!
# THE FOUNDATION STONE — TEST 1: WHAT IS STORED, WHAT IS EARNED

Charlie's question: do the formal B-stations FORCE the diagonal, or was the diagonal
placed inside them? This file tests the certified Stage 2 predicates (Idol.lean,
lines 62–82), copied with two mechanical changes:
  * `T^[n]` is written `iter T n` (the same function; core Lean has no `^[ ]`);
  * the finite windows in `finuniversal` are lists, not Finsets. No proof below looks
    inside a window, so every argument transfers word for word.

Order of results:
1. The diagonal with no Idol words: a move with no still point defeats every complete
   self-listing (Cantor / Lawvere).
2. EARNED. Formal B7 is EXACTLY that diagonal for the wall's own moves:
   B7 ↔ the wall cannot index all of its own moves by its own points.
   The flip B9 is itself the diagonal operator for that listing. In this frame B9 ↔ B12.
   Thin: B7 holds exactly when the wall has other than one point.
3. FOOL'S GOLD. `All12 S → no complete table for reachability` is B1 read back out.
4. STORED (red controls). Starting from ANY system:
   * add one table to the codebook: only B1 breaks;
   * give the language names for its invariants: only B3 and B11 break;
   * silence the proof predicate: B5 becomes true.
   So B1, B3 and B11 are not produced by the other stations, and B5 is met by saying
   nothing at all.
5. SIDE BY SIDE. On the certified wall ℕ × Bool the flip never touches the address, so
   every address predicate — the Tarski truth-set among them — is flip-invariant for
   free. Standing still keeps them invariant too.
6. A CANDIDATE FOUNDATION STONE (amber). If the flip reverses every reading, the flip
   alone forces B9, B12, B2, and forbids naming any invariant: namelessness EARNED
   rather than stored. The magenta line on the clock is an instance. Whether this can
   sit inside a full twelve-station system is Test 2.
-/
namespace FoundationStone

/-! ## Part 0 — the Stage 2 signature, copied -/

def iter {X : Type} (T : X → X) : Nat → X → X
  | 0, x => x
  | n + 1, x => T (iter T n x)

structure System where
  X : Type
  T : X → X
  Φ : Type
  φ : Φ
  L : Type
  falsum : L
  con : L
  den : L → X → Prop
  Prf : L → Prop
  R : X → X → Prop
  C : X → X → X
  interp : Nat → X → X → Bool
  finuniversal : ∀ Q : X → X → Prop, (∀ x y, Decidable (Q x y)) →
    ∀ K : List X, ∃ e, ∀ x ∈ K, ∀ y ∈ K, interp e x y = true ↔ Q x y

def Invariant {X : Type} (T : X → X) (I : X → Prop) : Prop := ∀ x, I x → I (T x)
def Reachable {X : Type} (T : X → X) (x y : X) : Prop := ∃ n, iter T n x = y
def CoOrbit {X : Type} (T : X → X) (x y : X) : Prop := ∃ n m, iter T n x = iter T m y
def Consistent (S : System) : Prop := ¬ S.Prf S.falsum

namespace System
def B1 (S : System) : Prop := ¬ ∃ e : Nat, ∀ x y, S.interp e x y = true ↔ Reachable S.T x y
def B2 (S : System) : Prop :=
  ∃ x : S.X, S.T x ≠ x ∧
    ∀ ℓ : S.L, S.den ℓ x → ∀ n, ∃ m, n < m ∧ S.den ℓ (iter S.T m x)
def B3 (S : System) : Prop :=
  ∃ I : S.X → Prop, Invariant S.T I ∧
    (∀ x, I x → ∃ y, I y ∧ S.T y = x) ∧ ¬ ∃ ℓ : S.L, ∀ x, S.den ℓ x ↔ I x
def B4 (S : System) : Prop := ∀ x y, S.R x y ↔ CoOrbit S.T x y
def B5 (S : System) : Prop := Consistent S ∧ ¬ S.Prf S.con
def B6 (S : System) : Prop := ∃ φ' : S.Φ, φ' ≠ S.φ
def B7 (S : System) : Prop := ∃ F : S.X → S.X, ∀ x, F x ≠ x
def B8 (S : System) : Prop :=
  ∃ K : S.X → Prop, (∃ a, K a) ∧ (∃ b, ¬ K b) ∧
    (∀ x y, K x → K (S.C x y)) ∧ (∀ x y, K (S.C x y) → K x ∨ K y)
def B9 (S : System) : Prop := ∀ x, S.T x ≠ x
def B10 (S : System) : Prop :=
  Function.Injective S.T ∧ ∃ ℓ : S.L, ∃ x, S.den ℓ x ∧ ¬ ∀ y, S.den ℓ y
def B11 (S : System) : Prop :=
  ∃ I : S.X → Prop, Invariant S.T I ∧
    I ≠ (fun _ => False) ∧ I ≠ (fun _ => True) ∧ ¬ ∃ ℓ : S.L, ∀ x, S.den ℓ x ↔ I x
def B12 (S : System) : Prop := ∀ x, ∃ n y, 0 < n ∧ iter S.T n x = y ∧ S.T y ≠ y
end System

structure All12 (S : System) : Prop where
  b1 : S.B1
  b2 : S.B2
  b3 : S.B3
  b4 : S.B4
  b5 : S.B5
  b6 : S.B6
  b7 : S.B7
  b8 : S.B8
  b9 : S.B9
  b10 : S.B10
  b11 : S.B11
  b12 : S.B12

/-! ## Part 1 — the diagonal, with no Idol words -/

/-- A listing of the functions `A → B`, indexed by `A`, is complete when every function
appears somewhere in it. -/
def CompleteListing {A B : Type} (e : A → A → B) : Prop := ∀ g : A → B, ∃ a, e a = g

/-- 1. A move on `B` with no still point defeats every complete listing. -/
theorem diagonal {A B : Type} (f : B → B) (hf : ∀ b, f b ≠ b) (e : A → A → B) :
    ¬ CompleteListing e := by
  intro he
  obtain ⟨a, ha⟩ := he (fun a => f (e a a))
  exact hf (e a a) (congrFun ha a).symm

/-! ## Part 2 — EARNED: B7 is the diagonal for the wall's own moves -/

theorem two_points_give_a_flip {X : Type} {a b : X} (h : a ≠ b) :
    ∃ F : X → X, ∀ x, F x ≠ x := by
  classical
  refine ⟨fun x => if x = a then b else a, fun x => ?_⟩
  show (if x = a then b else a) ≠ x
  by_cases hx : x = a
  · simp only [hx, ite_true]; exact fun e => h e.symm
  · simp only [hx, ite_false]; exact fun e => hx e.symm

/-- 2a. Formal B7 is EXACTLY the diagonal obstruction for the wall indexing its own moves
by its own points. -/
theorem B7_iff_no_complete_self_listing (S : System) :
    S.B7 ↔ ∀ e : S.X → S.X → S.X, ¬ CompleteListing e := by
  constructor
  · intro ⟨F, hF⟩ e
    exact diagonal F hF e
  · intro h
    apply Classical.byContradiction
    intro hn
    have hsub : ∀ a b : S.X, a = b := fun a b =>
      Classical.byContradiction fun hab => hn (two_points_give_a_flip hab)
    have hne : Nonempty S.X := Classical.byContradiction fun hx =>
      hn ⟨id, fun x => absurd ⟨x⟩ hx⟩
    obtain ⟨x₀⟩ := hne
    exact h (fun _ => id) (fun g => ⟨x₀, funext fun x => hsub x (g x)⟩)

/-- 2b. The flip itself is the diagonal operator: B9 alone refutes every complete listing
of the wall's moves by its points. -/
theorem flip_is_the_diagonal_operator (S : System) (h9 : S.B9) (e : S.X → S.X → S.X) :
    ¬ CompleteListing e :=
  diagonal S.T h9 e

theorem iter_still {X : Type} {T : X → X} {x : X} (hx : T x = x) : ∀ n, iter T n x = x
  | 0 => rfl
  | n + 1 => by show T (iter T n x) = x; rw [iter_still hx n]; exact hx

/-- 2c. In the Stage 2 frame, the release (B9) and the reception (B12) are one station. -/
theorem B9_iff_B12 (S : System) : S.B9 ↔ S.B12 := by
  constructor
  · intro h9 x
    exact ⟨1, S.T x, Nat.one_pos, rfl, h9 (S.T x)⟩
  · intro h12 x hx
    obtain ⟨n, y, _, hy, hTy⟩ := h12 x
    rw [iter_still hx n] at hy
    subst hy
    exact hTy hx

/-! ## Part 3 — FOOL'S GOLD -/

/-- 3. The theorem the test hopes for, obtained by reading B1 back out. Worthless as
evidence: it is stored, not earned. -/
theorem fools_gold (S : System) (h : All12 S) :
    ¬ ∃ e : Nat, ∀ x y, S.interp e x y = true ↔ Reachable S.T x y :=
  h.b1

/-! ## Part 4 — STORED: three red controls -/

/-- Add one table, code 0, that decides reachability exactly; shift the old codebook up
by one. Nothing else changes. -/
noncomputable def withDecider (S : System) : System where
  X := S.X
  T := S.T
  Φ := S.Φ
  φ := S.φ
  L := S.L
  falsum := S.falsum
  con := S.con
  den := S.den
  Prf := S.Prf
  R := S.R
  C := S.C
  interp := fun e x y => match e with
    | 0 => @decide (Reachable S.T x y) (Classical.propDecidable _)
    | e + 1 => S.interp e x y
  finuniversal := by
    intro Q hQ K
    obtain ⟨e, he⟩ := S.finuniversal Q hQ K
    exact ⟨e + 1, fun x hx y hy => he x hx y hy⟩

structure AllBut1 (S : System) : Prop where
  b2 : S.B2
  b3 : S.B3
  b4 : S.B4
  b5 : S.B5
  b6 : S.B6
  b7 : S.B7
  b8 : S.B8
  b9 : S.B9
  b10 : S.B10
  b11 : S.B11
  b12 : S.B12

/-- 4a. One extra table: the other eleven stand, B1 falls. -/
theorem B1_is_stored (S : System) (h : AllBut1 S) :
    AllBut1 (withDecider S) ∧ ¬ (withDecider S).B1 :=
  ⟨⟨h.b2, h.b3, h.b4, h.b5, h.b6, h.b7, h.b8, h.b9, h.b10, h.b11, h.b12⟩,
   fun h1 => h1 ⟨0, fun _ _ => @decide_eq_true_iff _ (Classical.propDecidable _)⟩⟩

/-- 4a'. So if any system meets the other eleven (Stage 2's certified wall does), they do
not force B1. -/
theorem B1_not_forced (hex : ∃ S, AllBut1 S) : ¬ ∀ S, AllBut1 S → S.B1 := by
  intro hall
  obtain ⟨S, hS⟩ := hex
  have ⟨h', hno⟩ := B1_is_stored S hS
  exact hno (hall _ h')

/-- Give the language a name for every invariant. Proof is unchanged on old names; the
new names prove nothing. -/
def named (S : System) : System where
  X := S.X
  T := S.T
  Φ := S.Φ
  φ := S.φ
  L := Sum S.L {I : S.X → Prop // Invariant S.T I}
  falsum := .inl S.falsum
  con := .inl S.con
  den := fun ℓ x => match ℓ with
    | .inl ℓ => S.den ℓ x
    | .inr I => I.val x
  Prf := fun ℓ => match ℓ with
    | .inl ℓ => S.Prf ℓ
    | .inr _ => False
  R := S.R
  C := S.C
  interp := S.interp
  finuniversal := S.finuniversal

theorem Invariant.along {X : Type} {T : X → X} {I : X → Prop} (h : Invariant T I)
    {x : X} (hx : I x) : ∀ n, I (iter T n x)
  | 0 => hx
  | n + 1 => h _ (Invariant.along h hx n)

theorem named_keeps_B2 (S : System) (h : S.B2) : (named S).B2 := by
  obtain ⟨x, hx, hrec⟩ := h
  refine ⟨x, hx, fun ℓ hℓ n => ?_⟩
  match ℓ, hℓ with
  | .inl ℓ, hℓ => exact hrec ℓ hℓ n
  | .inr I, hℓ => exact ⟨n + 1, Nat.lt_succ_self n, Invariant.along I.property hℓ (n + 1)⟩

theorem named_keeps_B10 (S : System) (h : S.B10) : (named S).B10 := by
  obtain ⟨hinj, ℓ, x, hx, hnot⟩ := h
  exact ⟨hinj, .inl ℓ, x, hx, hnot⟩

theorem named_breaks_B3 (S : System) : ¬ (named S).B3 := by
  intro ⟨I, hI, _, hnm⟩
  exact hnm ⟨.inr ⟨I, hI⟩, fun _ => Iff.rfl⟩

theorem named_breaks_B11 (S : System) : ¬ (named S).B11 := by
  intro ⟨I, hI, _, _, hnm⟩
  exact hnm ⟨.inr ⟨I, hI⟩, fun _ => Iff.rfl⟩

structure AllBut3and11 (S : System) : Prop where
  b1 : S.B1
  b2 : S.B2
  b4 : S.B4
  b5 : S.B5
  b6 : S.B6
  b7 : S.B7
  b8 : S.B8
  b9 : S.B9
  b10 : S.B10
  b12 : S.B12

/-- 4b. Names for the invariants: the other ten stand, B3 and B11 fall. -/
theorem B3_B11_are_stored (S : System) (h : AllBut3and11 S) :
    AllBut3and11 (named S) ∧ ¬ (named S).B3 ∧ ¬ (named S).B11 :=
  ⟨⟨h.b1, named_keeps_B2 S h.b2, h.b4, ⟨h.b5.1, h.b5.2⟩, h.b6, h.b7, h.b8, h.b9,
    named_keeps_B10 S h.b10, h.b12⟩,
   named_breaks_B3 S, named_breaks_B11 S⟩

/-- Silence: the proof predicate proves nothing. -/
def mute (S : System) : System where
  X := S.X
  T := S.T
  Φ := S.Φ
  φ := S.φ
  L := S.L
  falsum := S.falsum
  con := S.con
  den := S.den
  Prf := fun _ => False
  R := S.R
  C := S.C
  interp := S.interp
  finuniversal := S.finuniversal

structure AllBut5 (S : System) : Prop where
  b1 : S.B1
  b2 : S.B2
  b3 : S.B3
  b4 : S.B4
  b6 : S.B6
  b7 : S.B7
  b8 : S.B8
  b9 : S.B9
  b10 : S.B10
  b11 : S.B11
  b12 : S.B12

/-- 4c. A system that proves nothing meets B5: formal B5 cannot tell Gödel's silence
from muteness. -/
theorem muteness_meets_B5 (S : System) : (mute S).B5 :=
  ⟨fun h => h, fun h => h⟩

theorem muteness_completes_the_twelve (S : System) (h : AllBut5 S) : All12 (mute S) :=
  ⟨h.b1, h.b2, h.b3, h.b4, muteness_meets_B5 S, h.b6, h.b7, h.b8, h.b9, h.b10, h.b11,
   h.b12⟩

/-! ## Part 5 — SIDE BY SIDE: the flip and the address never meet -/

/-- The certified wall's flip: address `n` kept, side `b` turned over. -/
def Tf (p : Nat × Bool) : Nat × Bool := (p.1, !p.2)

theorem flip_never_touches_the_address : ∀ p : Nat × Bool, (Tf p).1 = p.1 :=
  fun _ => rfl

/-- 5a. Any move that keeps the address keeps every address predicate invariant. -/
theorem address_keeping_moves_keep_address_predicates (U : Nat × Bool → Nat × Bool)
    (hU : ∀ p, (U p).1 = p.1) (P : Nat → Prop) : Invariant U (fun p => P p.1) := by
  intro p hp
  show P (U p).1
  rw [hU p]
  exact hp

/-- 5b. So the flip keeps every address predicate, the truth-set among them... -/
theorem flip_keeps_every_address_predicate (P : Nat → Prop) :
    Invariant Tf (fun p => P p.1) :=
  address_keeping_moves_keep_address_predicates Tf flip_never_touches_the_address P

/-- 5c. ...and so does standing still. The invariance owes nothing to the flip. -/
theorem stillness_keeps_every_address_predicate (P : Nat → Prop) :
    Invariant (fun p => p) (fun p : Nat × Bool => P p.1) :=
  address_keeping_moves_keep_address_predicates (fun p => p) (fun _ => rfl) P

/-! ## Part 6 — AMBER: a candidate foundation stone -/

/-- The flip reverses every reading: whatever a name says of a point, it denies of the
flipped point. -/
def ReversesReadings {X L : Type} (T : X → X) (den : L → X → Prop) : Prop :=
  ∀ ℓ x, den ℓ (T x) ↔ ¬ den ℓ x

/-- 6a. Reversal forbids a still point: it forces B9 (one name is enough). -/
theorem reversal_forbids_stillness {X L : Type} (T : X → X) (den : L → X → Prop)
    (hR : ReversesReadings T den) (ℓ : L) : ∀ x, T x ≠ x := by
  intro x hx
  have h := hR ℓ x
  rw [hx] at h
  have hn : ¬ den ℓ x := fun hd => h.mp hd hd
  exact hn (h.mpr hn)

/-- 6b. Reversal hides every invariant: no name can say what the flip leaves unchanged. -/
theorem reversal_hides_every_invariant {X L : Type} (T : X → X) (den : L → X → Prop)
    (hR : ReversesReadings T den) (I : X → Prop) (hI : Invariant T I) (x : X) :
    ¬ ∃ ℓ : L, ∀ y, den ℓ y ↔ I y := by
  intro ⟨ℓ, hℓ⟩
  have hnx : ¬ I x := fun hx =>
    (hR ℓ x).mp ((hℓ (T x)).mpr (hI x hx)) ((hℓ x).mpr hx)
  have hTx : I (T x) := (hℓ (T x)).mp ((hR ℓ x).mpr fun hd => hnx ((hℓ x).mp hd))
  exact (hR ℓ (T x)).mp ((hℓ (T (T x))).mpr (hI _ hTx)) ((hℓ (T x)).mpr hTx)

/-- Two reversals give the reading back. -/
theorem reversal_twice {X L : Type} {T : X → X} {den : L → X → Prop}
    (hR : ReversesReadings T den) (ℓ : L) (x : X) (h : den ℓ x) : den ℓ (T (T x)) :=
  (hR ℓ (T x)).mpr fun hT => (hR ℓ x).mp hT h

theorem reversal_even {X L : Type} {T : X → X} {den : L → X → Prop}
    (hR : ReversesReadings T den) (ℓ : L) (x : X) (h : den ℓ x) :
    ∀ k, den ℓ (iter T (2 * k) x)
  | 0 => h
  | k + 1 => by
    show den ℓ (T (T (iter T (2 * k) x)))
    exact reversal_twice hR ℓ _ (reversal_even hR ℓ x h k)

/-- 6c. In a full system, reversal alone earns B9, B12 and B2 ... -/
theorem reversal_earns_B9_B12_B2 (S : System) (hR : ReversesReadings S.T S.den)
    (x : S.X) : S.B9 ∧ S.B12 ∧ S.B2 := by
  have h9 : S.B9 := reversal_forbids_stillness S.T S.den hR S.falsum
  refine ⟨h9, (B9_iff_B12 S).mp h9, x, h9 x, fun ℓ hℓ n => ?_⟩
  exact ⟨2 * (n + 1), by omega, reversal_even hR ℓ x hℓ (n + 1)⟩

/-- 6d. ... and, given any invariant that is sometimes true and sometimes false, B11. -/
theorem reversal_earns_B11 (S : System) (hR : ReversesReadings S.T S.den)
    (I : S.X → Prop) (hI : Invariant S.T I) (a b : S.X) (ha : I a) (hb : ¬ I b) :
    S.B11 := by
  refine ⟨I, hI, ?_, ?_, reversal_hides_every_invariant S.T S.den hR I hI a⟩
  · intro h
    rw [h] at ha
    exact ha
  · intro h
    rw [h] at hb
    exact hb trivial

/-- The magenta line on the clock: seat `k` goes to `11 − k`. -/
def magenta (k : Fin 12) : Fin 12 := 11 - k

def truthChart (k : Fin 12) : Bool :=
  match k.val with
  | 1 | 3 | 4 | 5 | 9 | 11 => true
  | _ => false

/-- One name: "this seat is on the truth chart". -/
def chartReads (_ : Unit) (k : Fin 12) : Prop := truthChart k = true

/-- 6e. An instance: the magenta line reverses the chart reading. -/
theorem magenta_reverses_the_chart : ReversesReadings magenta chartReads := by
  intro _ k
  show truthChart (11 - k) = true ↔ ¬ truthChart k = true
  revert k
  decide

/-- 6f. So the chart cannot name the pair magenta swaps: {B12, B11}. -/
theorem chart_cannot_name_the_magenta_pair :
    ¬ ∃ ℓ : Unit, ∀ k, chartReads ℓ k ↔ (k = 0 ∨ k = 11) := by
  apply reversal_hides_every_invariant magenta chartReads magenta_reverses_the_chart
    (fun k => k = 0 ∨ k = 11) _ 0
  intro k hk
  show (11 - k = 0 ∨ 11 - k = 11)
  revert k
  decide

/-! ## The certificate -/

theorem foundation_stone_test_one :
    (∀ S : System, S.B7 ↔ ∀ e : S.X → S.X → S.X, ¬ CompleteListing e) ∧
    (∀ S : System, S.B9 ↔ S.B12) ∧
    (∀ S : System, AllBut1 S → AllBut1 (withDecider S) ∧ ¬ (withDecider S).B1) ∧
    (∀ S : System, AllBut3and11 S →
      AllBut3and11 (named S) ∧ ¬ (named S).B3 ∧ ¬ (named S).B11) ∧
    (∀ S : System, AllBut5 S → All12 (mute S)) ∧
    (∀ P : Nat → Prop, Invariant (fun p => p) (fun p : Nat × Bool => P p.1)) ∧
    (∀ S : System, ReversesReadings S.T S.den → S.X → S.B9 ∧ S.B12 ∧ S.B2) ∧
    ReversesReadings magenta chartReads :=
  ⟨B7_iff_no_complete_self_listing, B9_iff_B12, B1_is_stored, B3_B11_are_stored,
   muteness_completes_the_twelve, stillness_keeps_every_address_predicate,
   reversal_earns_B9_B12_B2, magenta_reverses_the_chart⟩

#print axioms diagonal
#print axioms B7_iff_no_complete_self_listing
#print axioms flip_is_the_diagonal_operator
#print axioms B9_iff_B12
#print axioms fools_gold
#print axioms B1_is_stored
#print axioms B3_B11_are_stored
#print axioms muteness_completes_the_twelve
#print axioms stillness_keeps_every_address_predicate
#print axioms reversal_hides_every_invariant
#print axioms reversal_earns_B9_B12_B2
#print axioms reversal_earns_B11
#print axioms magenta_reverses_the_chart
#print axioms chart_cannot_name_the_magenta_pair
#print axioms foundation_stone_test_one

end FoundationStone
