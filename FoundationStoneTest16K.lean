/-!
# THE FIVE REPAIRS — FOUNDATION STONE TEST 16K

Runs in the Lean live editor with no imports (core Lean only).

Test 16J proved that the native signed B6 can coexist with the other eleven,
but also exposed a projection trap: the old predicates do not inspect the
frame.  Test 16K writes the specification gate for the five predicates that
currently carry too much interpretation: B1, B3, B5, B7 and B11.

This file does NOT claim Gödel, Tarski or Turing for the Wooden Idol.  It does
three more basic and necessary jobs:

1. It states the additional interfaces a later proof must actually use:
   an indexed computation model for B1; a fixed negation-closed language and
   semantic diagonal for B3/B11; a non-mute arithmetised proof system with the
   Hilbert-Bernays-Löb derivability conditions for B5; and an explicit
   self-application evaluator for B7.
2. It proves the generic diagonal and Tarski obstructions from those interfaces.
3. It gives red controls showing that every old predicate can pass while a key
   part of its intended interface is absent.

Thus a later green counts only if it crosses this gate.  Merely copying the old
conclusion into a field no longer qualifies.
-/
namespace FoundationStoneTest16K

/-! ## Common dynamics and the five legacy shapes -/

def iter {X : Type} (T : X -> X) : Nat -> X -> X
  | 0, x => x
  | n + 1, x => T (iter T n x)

def Reachable {X : Type} (T : X -> X) (x y : X) : Prop :=
  exists n, iter T n x = y

def Invariant {X : Type} (T : X -> X) (I : X -> Prop) : Prop :=
  forall x, I x -> I (T x)

def BackwardClosed {X : Type} (T : X -> X) (I : X -> Prop) : Prop :=
  forall x, I x -> exists y, I y /\ T y = x

def Names {X L : Type} (den : L -> X -> Prop) (I : X -> Prop) : Prop :=
  exists ell : L, forall x, den ell x <-> I x

def LegacyB1 {X : Type} (T : X -> X) (interp : Nat -> X -> X -> Bool) : Prop :=
  ¬ exists e, forall x y, interp e x y = true <-> Reachable T x y

def LegacyB3 {X L : Type} (T : X -> X) (den : L -> X -> Prop) : Prop :=
  exists I, Invariant T I /\ BackwardClosed T I /\ ¬ Names den I

def LegacyB5 {L : Type} (Prf : L -> Prop) (falsum con : L) : Prop :=
  (¬ Prf falsum) /\ ¬ Prf con

def LegacyB7 (X : Type) : Prop :=
  exists flip : X -> X, forall x, flip x ≠ x

def LegacyB11 {X L : Type} (T : X -> X) (den : L -> X -> Prop) : Prop :=
  exists I, Invariant T I /\ I ≠ (fun _ => False) /\
    I ≠ (fun _ => True) /\ ¬ Names den I

/-! ## Repair 1 — B1 must quantify over an effective code model -/

def DecidesReachability {X : Type} (T : X -> X) (d : X -> X -> Bool) : Prop :=
  forall x y, d x y = true <-> Reachable T x y

/-- A declared computability class together with a numbered evaluator that is
complete for that class.  A real instantiation must justify `Computable`; it
may not define it as whatever makes the theorem convenient. -/
structure ComputationFrame (X : Type) where
  Computable : (X -> X -> Bool) -> Prop
  run : Nat -> X -> X -> Option Bool
  captures : forall d, Computable d -> exists e, forall x y, run e x y = some (d x y)

def CodeDecidesReachability {X : Type} (M : ComputationFrame X)
    (T : X -> X) (e : Nat) : Prop :=
  forall x y, M.run e x y = some true <-> Reachable T x y

def RepairedB1 {X : Type} (M : ComputationFrame X) (T : X -> X) : Prop :=
  ¬ exists e, CodeDecidesReachability M T e

/-- Once the evaluator really captures the declared computable functions,
repaired B1 rules out every computable reachability decider. -/
theorem repaired_B1_forbids_computable_decider {X : Type}
    (M : ComputationFrame X) (T : X -> X) (h1 : RepairedB1 M T)
    (d : X -> X -> Bool) (hd : M.Computable d) :
    ¬ DecidesReachability T d := by
  intro hdec
  obtain ⟨e, he⟩ := M.captures d hd
  apply h1
  refine ⟨e, fun x y => ?_⟩
  rw [he]
  simpa using hdec x y

/-! The B1 red control: an impoverished codebook says `false` everywhere even
though the dynamics is explicitly decidable. -/

def boolFlip (b : Bool) : Bool := !b
def poorInterp (_ : Nat) (_ _ : Bool) : Bool := false
def externalReach (_ _ : Bool) : Bool := true

theorem bool_flip_reaches_everywhere : forall x y : Bool, Reachable boolFlip x y := by
  intro x y
  cases x <;> cases y
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨0, rfl⟩

theorem poor_codebook_passes_legacy_B1 : LegacyB1 boolFlip poorInterp := by
  intro h
  obtain ⟨e, he⟩ := h
  have bad := (he false false).mpr (bool_flip_reaches_everywhere false false)
  simp [poorInterp] at bad

theorem external_reachability_decider_is_correct :
    DecidesReachability boolFlip externalReach := by
  intro x y
  constructor
  · intro _
    exact bool_flip_reaches_everywhere x y
  · intro _
    rfl

theorem legacy_B1_does_not_mean_undecidable :
    LegacyB1 boolFlip poorInterp /\
    exists d, DecidesReachability boolFlip d :=
  ⟨poor_codebook_passes_legacy_B1,
   ⟨externalReach, external_reachability_decider_is_correct⟩⟩

/-! ## Repairs 2 and 5 — B3/B11 need a fixed expressive language -/

/-- The minimum Boolean language interface.  Tarski needs substantially more
than an empty vocabulary: at least semantic negation, and for the arithmetic
instance a justified coding/diagonal lemma. -/
structure BooleanLanguage (X L : Type) (den : L -> X -> Prop) where
  top : L
  bot : L
  neg : L -> L
  top_spec : forall x, den top x
  bot_spec : forall x, ¬ den bot x
  neg_spec : forall ell x, den (neg ell) x <-> ¬ den ell x

def RepairedB3 {X L : Type} (T : X -> X) (den : L -> X -> Prop)
    (_lang : BooleanLanguage X L den) (I : X -> Prop) : Prop :=
  Invariant T I /\ BackwardClosed T I /\ ¬ Names den I

def RepairedB11 {X L : Type} (T : X -> X) (den : L -> X -> Prop)
    (_lang : BooleanLanguage X L den) (I : X -> Prop) : Prop :=
  Invariant T I /\ I ≠ (fun _ => False) /\ I ≠ (fun _ => True) /\ ¬ Names den I

/-- A semantic diagonal interface.  This is the common Lawvere/Tarski skeleton;
an arithmetic instance must construct it from syntax rather than postulate its
conclusion. -/
structure TarskiFrame where
  Sentence : Type
  Formula : Type
  Code : Type
  quote : Sentence -> Code
  trueOf : Sentence -> Prop
  sat : Formula -> Code -> Prop
  neg : Formula -> Formula
  neg_spec : forall phi c, sat (neg phi) c <-> ¬ sat phi c
  diagonal : forall phi, exists sigma, trueOf sigma <-> sat phi (quote sigma)

def NamesTruth (F : TarskiFrame) : Prop :=
  exists truthFormula : F.Formula,
    forall sigma, F.sat truthFormula (F.quote sigma) <-> F.trueOf sigma

/-- The Tarski obstruction is now earned from fixed-language negation plus the
semantic diagonal lemma. -/
theorem tarski_undefinable (F : TarskiFrame) : ¬ NamesTruth F := by
  intro hname
  obtain ⟨tau, htau⟩ := hname
  obtain ⟨sigma, hdiag⟩ := F.diagonal (F.neg tau)
  have liar : F.trueOf sigma <-> ¬ F.trueOf sigma := by
    constructor
    · intro hs
      have hnSat : ¬ F.sat tau (F.quote sigma) :=
        (F.neg_spec tau (F.quote sigma)).mp (hdiag.mp hs)
      intro hs'
      exact hnSat ((htau sigma).mpr hs')
    · intro hns
      apply hdiag.mpr
      apply (F.neg_spec tau (F.quote sigma)).mpr
      intro hsat
      exact hns ((htau sigma).mp hsat)
  have hn : ¬ F.trueOf sigma := fun hs => (liar.mp hs) hs
  exact hn (liar.mpr hn)

/-! The B3/B11 red control: a one-word language that says nothing. -/

def still (b : Bool) : Bool := b
def target (b : Bool) : Prop := b = true
def poorDen (_ : Unit) (_ : Bool) : Prop := False

theorem target_invariant : Invariant still target := by
  intro x hx
  exact hx

theorem target_backward : BackwardClosed still target := by
  intro x hx
  exact ⟨x, hx, rfl⟩

theorem poor_language_cannot_name_target : ¬ Names poorDen target := by
  intro h
  obtain ⟨ell, hell⟩ := h
  have bad := (hell true).mpr rfl
  exact bad

theorem poor_language_passes_legacy_B3 : LegacyB3 still poorDen :=
  ⟨target, target_invariant, target_backward, poor_language_cannot_name_target⟩

theorem target_not_false : target ≠ (fun _ => False) := by
  intro h
  have bad := congrFun h true
  simp [target] at bad

theorem target_not_true : target ≠ (fun _ => True) := by
  intro h
  have bad := congrFun h false
  simp [target] at bad

theorem poor_language_passes_legacy_B11 : LegacyB11 still poorDen :=
  ⟨target, target_invariant, target_not_false, target_not_true,
   poor_language_cannot_name_target⟩

/-- The silent language cannot even supply Boolean negation, so its
unnameability is not Tarski-strength. -/
theorem poor_language_has_no_boolean_structure :
    ¬ Nonempty (BooleanLanguage Bool Unit poorDen) := by
  intro h
  obtain ⟨lang⟩ := h
  exact lang.bot_spec true (lang.top_spec true)

/-! ## Repair 3 — B5 needs a non-mute arithmetised proof system -/

def Productive {L : Type} (Prf : L -> Prop) : Prop := exists p, Prf p

/-- A Gödel-II-ready signature.  The three `d` fields are the standard
Hilbert-Bernays-Löb derivability conditions, expressed inside the chosen
sentence calculus.  A full instance must also justify that calculus and its
arithmetisation. -/
structure GodelFrame where
  Sentence : Type
  Prf : Sentence -> Prop
  falsum : Sentence
  con : Sentence
  imp : Sentence -> Sentence -> Sentence
  neg : Sentence -> Sentence
  prov : Sentence -> Sentence
  con_is_not_provable_falsum : con = neg (prov falsum)
  productive : Productive Prf
  d1 : forall p, Prf p -> Prf (prov p)
  d2 : forall p q, Prf (imp (prov (imp p q)) (imp (prov p) (prov q)))
  d3 : forall p, Prf (imp (prov p) (prov (prov p)))

def RepairedB5 (G : GodelFrame) : Prop :=
  (¬ G.Prf G.falsum) /\ ¬ G.Prf G.con

def mutePrf (_ : Unit) : Prop := False

theorem mute_passes_legacy_B5 : LegacyB5 mutePrf () () := by
  exact ⟨fun h => h, fun h => h⟩

theorem mute_is_not_productive : ¬ Productive mutePrf := by
  intro h
  obtain ⟨p, hp⟩ := h
  exact hp

theorem legacy_B5_does_not_mean_Godel :
    LegacyB5 mutePrf () () /\ ¬ Productive mutePrf :=
  ⟨mute_passes_legacy_B5, mute_is_not_productive⟩

/-! ## Repair 4 — B7 needs explicit coding, evaluation and self-application -/

structure SelfApplication (X : Type) where
  Code : Type
  eval : Code -> Code -> X
  flip : X -> X
  flip_no_fixed : forall x, flip x ≠ x

def diagonal {X : Type} (S : SelfApplication X) (c : S.Code) : X :=
  S.flip (S.eval c c)

def RepairedB7 {X : Type} (S : SelfApplication X) : Prop :=
  Nonempty S.Code /\ forall c, S.eval c c ≠ diagonal S c

/-- The real diagonal step: no code's diagonal entry equals the flipped
self-application value. -/
theorem self_application_diagonal {X : Type} (S : SelfApplication X) :
    forall c, S.eval c c ≠ diagonal S c := by
  intro c h
  exact S.flip_no_fixed (S.eval c c) h.symm

theorem bool_has_legacy_B7 : LegacyB7 Bool := by
  refine ⟨boolFlip, ?_⟩
  intro b
  cases b <;> decide

/-- The same state flip paired with an empty code language: legacy B7 still
holds, but there is no self-description to diagonalise. -/
def emptySelfApplication : SelfApplication Bool where
  Code := Empty
  eval := fun c => nomatch c
  flip := boolFlip
  flip_no_fixed := by intro b; cases b <;> decide

theorem empty_code_language_fails_repaired_B7 :
    ¬ RepairedB7 emptySelfApplication := by
  intro h
  obtain ⟨c⟩ := h.1
  exact nomatch c

/-- Positive control: once an inhabited evaluator is supplied, the diagonal
obstruction is earned rather than merely named. -/
def boolSelfApplication : SelfApplication Bool where
  Code := Unit
  eval := fun _ _ => false
  flip := boolFlip
  flip_no_fixed := by intro b; cases b <;> decide

theorem populated_code_language_passes_repaired_B7 :
    RepairedB7 boolSelfApplication :=
  ⟨⟨()⟩, self_application_diagonal boolSelfApplication⟩

/-! ## The five-part specification certificate -/

theorem five_repairs_certificate :
    (LegacyB1 boolFlip poorInterp /\
      exists d, DecidesReachability boolFlip d) /\
    (LegacyB3 still poorDen /\ ¬ Nonempty (BooleanLanguage Bool Unit poorDen)) /\
    (LegacyB5 mutePrf () () /\ ¬ Productive mutePrf) /\
    (LegacyB7 Bool /\ ¬ RepairedB7 emptySelfApplication /\
      RepairedB7 boolSelfApplication) /\
    (LegacyB11 still poorDen /\ ¬ Nonempty (BooleanLanguage Bool Unit poorDen)) /\
    (forall F : TarskiFrame, ¬ NamesTruth F) :=
  ⟨legacy_B1_does_not_mean_undecidable,
   ⟨poor_language_passes_legacy_B3, poor_language_has_no_boolean_structure⟩,
   legacy_B5_does_not_mean_Godel,
   ⟨bool_has_legacy_B7, empty_code_language_fails_repaired_B7,
    populated_code_language_passes_repaired_B7⟩,
   ⟨poor_language_passes_legacy_B11, poor_language_has_no_boolean_structure⟩,
   tarski_undefinable⟩

#print axioms repaired_B1_forbids_computable_decider
#print axioms legacy_B1_does_not_mean_undecidable
#print axioms tarski_undefinable
#print axioms poor_language_passes_legacy_B3
#print axioms poor_language_passes_legacy_B11
#print axioms poor_language_has_no_boolean_structure
#print axioms legacy_B5_does_not_mean_Godel
#print axioms self_application_diagonal
#print axioms bool_has_legacy_B7
#print axioms empty_code_language_fails_repaired_B7
#print axioms populated_code_language_passes_repaired_B7
#print axioms five_repairs_certificate

end FoundationStoneTest16K
