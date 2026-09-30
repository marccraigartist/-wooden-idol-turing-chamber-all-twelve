import Mathlib

/-!
# THE TURING CHAMBER — TEST 16AJ: FOUR STACKS, TWO COUNTERS

Lean 4.35.0-rc2 / Mathlib.

This file packages the four stacks of Mathlib's TM2 evaluator into the state
shape of a two-counter machine.  No additional unbounded store is introduced:

* the finite control (label and five-valued local variable) is encoded in `pc`;
* all four stacks are nested into counter `a`;
* counter `b` is exactly zero, available as scratch space.

The stack alphabet has four symbols and uses 16AI's base-five/end-marker code.
Natural-number pairing then packages the four stack codes.

Lean certifies that stack packing, control packing and the complete
configuration encoding are injective.  Hence no TM2 distinction is forgotten
at the entrance to the two-counter chamber.
-/

namespace FoundationStoneTest16AJ

abbrev Digit := Fin 4
abbrev Local := Fin 5

def stackCode : List Digit → Nat
  | [] => 0
  | d :: rest => (d.val + 1) + 5 * stackCode rest

def topCode (n : Nat) : Nat := (n - 1) % 5
def popCode (n : Nat) : Nat := (n - 1) / 5

theorem stackCode_cons_pos (d : Digit) (s : List Digit) :
    0 < stackCode (d :: s) := by
  unfold stackCode
  omega

theorem stackCode_eq_zero_iff (s : List Digit) :
    stackCode s = 0 ↔ s = [] := by
  cases s with
  | nil => simp [stackCode]
  | cons d rest =>
      constructor
      · intro h
        have := stackCode_cons_pos d rest
        omega
      · intro h
        contradiction

theorem top_correct (d : Digit) (s : List Digit) :
    topCode (stackCode (d :: s)) = d.val := by
  unfold topCode stackCode
  have := d.isLt
  omega

theorem pop_correct (d : Digit) (s : List Digit) :
    popCode (stackCode (d :: s)) = stackCode s := by
  unfold popCode
  change (d.val + 1 + 5 * stackCode s - 1) / 5 = stackCode s
  have hd : d.val < 4 := d.isLt
  have hsub : d.val + 1 + 5 * stackCode s - 1 =
      d.val + 5 * stackCode s := by omega
  rw [hsub, Nat.add_mul_div_left _ _ (by decide)]
  rw [Nat.div_eq_of_lt (by omega), Nat.zero_add]

theorem stackCode_injective : Function.Injective stackCode := by
  intro xs
  induction xs with
  | nil =>
      intro ys h
      exact ((stackCode_eq_zero_iff ys).mp (by simpa [stackCode] using h.symm)).symm
  | cons d ds ih =>
      intro ys h
      cases ys with
      | nil =>
          have := stackCode_cons_pos d ds
          simp [stackCode] at h
      | cons e es =>
          have hv : d.val = e.val := by
            have ht := congrArg topCode h
            simpa [top_correct] using ht
          have hde : d = e := Fin.ext hv
          subst e
          have hp := congrArg popCode h
          have hrs : stackCode ds = stackCode es := by
            simpa [pop_correct] using hp
          exact congrArg (List.cons d) (ih hrs)

/-- The four named stacks used by Mathlib's evaluator. -/
structure FourStacks where
  main : List Digit
  rev : List Digit
  aux : List Digit
  stack : List Digit
deriving DecidableEq

/-- All four stack codes nested into one natural number. -/
def packStacks (s : FourStacks) : Nat :=
  Nat.pair (stackCode s.main)
    (Nat.pair (stackCode s.rev)
      (Nat.pair (stackCode s.aux) (stackCode s.stack)))

theorem packStacks_injective : Function.Injective packStacks := by
  intro s t h
  unfold packStacks at h
  have h1 := (Nat.pair_eq_pair.mp h)
  have h2 := Nat.pair_eq_pair.mp h1.2
  have h3 := Nat.pair_eq_pair.mp h2.2
  cases s
  cases t
  simp only [FourStacks.mk.injEq]
  exact ⟨stackCode_injective h1.1, stackCode_injective h2.1,
    stackCode_injective h3.1, stackCode_injective h3.2⟩

/-- Canonical finite control: halted, or a running label plus local variable. -/
inductive Control (q : Nat)
  | halt
  | run (label : Fin q) (store : Local)
deriving DecidableEq

/-- Zero means halt; running controls occupy positive paired addresses. -/
def controlCode {q : Nat} : Control q → Nat
  | .halt => 0
  | .run label store => Nat.pair label.val store.val + 1

theorem controlCode_run_pos {q : Nat} (l : Fin q) (v : Local) :
    0 < controlCode (.run l v) := by
  simp [controlCode]

theorem controlCode_injective {q : Nat} : Function.Injective (@controlCode q) := by
  intro x y h
  cases x with
  | halt =>
      cases y with
      | halt => rfl
      | run l v =>
          have := controlCode_run_pos l v
          simp [controlCode] at h
  | run l v =>
      cases y with
      | halt =>
          have := controlCode_run_pos l v
          simp [controlCode] at h
      | run l' v' =>
          simp only [controlCode, Nat.add_right_cancel_iff] at h
          have hp := Nat.pair_eq_pair.mp h
          have hl : l = l' := Fin.ext hp.1
          have hv : v = v' := Fin.ext hp.2
          subst l'; subst v'
          rfl

structure EncodableCfg (q : Nat) where
  ctrl : Control q
  tapes : FourStacks
deriving DecidableEq

/-- The target shape of the standard two-counter machine state. -/
structure CounterState where
  pc : Nat
  a : Nat
  b : Nat
deriving DecidableEq

/-- Entrance to the counter chamber: control in `pc`, four stacks in `a`,
and exactly-zero scratch in `b`. -/
def encodeCfg {q : Nat} (cfg : EncodableCfg q) : CounterState :=
  ⟨controlCode cfg.ctrl, packStacks cfg.tapes, 0⟩

theorem encodeCfg_scratch_zero {q : Nat} (cfg : EncodableCfg q) :
    (encodeCfg cfg).b = 0 := rfl

/-- No source distinction is lost at the entrance. -/
theorem encodeCfg_injective {q : Nat} : Function.Injective (@encodeCfg q) := by
  intro x y h
  have hpc := congrArg CounterState.pc h
  have ha := congrArg CounterState.a h
  have hc : x.ctrl = y.ctrl := controlCode_injective hpc
  have hs : x.tapes = y.tapes := packStacks_injective ha
  cases x
  cases y
  simp_all

/-! ## Red controls -/

/-- Forgetting one stack really destroys injectivity. -/
def forgetAux (s : FourStacks) : Nat :=
  Nat.pair (stackCode s.main)
    (Nat.pair (stackCode s.rev) (stackCode s.stack))

def zeroStacks : FourStacks := ⟨[], [], [], []⟩
def markedAux : FourStacks := ⟨[], [], [⟨0, by decide⟩], []⟩

theorem forgetting_aux_collapses :
    forgetAux zeroStacks = forgetAux markedAux := by decide

theorem forgetting_aux_not_injective : ¬ Function.Injective forgetAux := by
  intro h
  have heq := h forgetting_aux_collapses
  have hne : zeroStacks ≠ markedAux := by decide
  exact hne heq

theorem turing_chamber_16AJ_certificate :
    Function.Injective packStacks ∧
    (∀ q, Function.Injective (@controlCode q)) ∧
    (∀ q, Function.Injective (@encodeCfg q)) ∧
    (∀ q (c : EncodableCfg q), (encodeCfg c).b = 0) ∧
    ¬ Function.Injective forgetAux :=
  ⟨packStacks_injective, fun _ => controlCode_injective,
   fun _ => encodeCfg_injective, fun _ _ => rfl,
   forgetting_aux_not_injective⟩

#print axioms packStacks_injective
#print axioms controlCode_injective
#print axioms encodeCfg_injective
#print axioms forgetting_aux_not_injective
#print axioms turing_chamber_16AJ_certificate

end FoundationStoneTest16AJ
