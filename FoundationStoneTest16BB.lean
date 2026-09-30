import FoundationStoneTest16AY
import FoundationStoneTest16AV
import FoundationStoneTest16AW

/-!
# THE TURING CHAMBER — TEST 16BB: PRIMITIVE ARITHMETIC INSIDE FIVE COUNTERS

Lean 4.35.0-rc2 / pinned Mathlib.

This begins Layer B1 in earnest.  The four logical stack counters occupy
registers 0–3 of a primitive five-counter Minsky machine; register 4 is the
sole temporary counter.  The parametric primitive programs already verified
in 16AV and 16AW are transported into any selected stack register.

Lean proves a step-for-step embedding, then lifts it to arbitrary bounded
runs.  Consequently:

* multiplication by five consumes the selected stack into `T`;
* the transfer block restores `5*n` to the selected stack and restores `T=0`;
* division by five leaves the exact remainder in finite control and the
  quotient in `T`;
* the transfer block restores the quotient to the selected stack and `T=0`;
* every one of the other three logical counters is unchanged.

Thus one scratch counter is sufficient for the base-five arithmetic.  This
file intentionally stops before stitching the division and transfer label
spaces into one 16AY block family; that finite exit-patching is the next
compiler construction, not an assumed equality here.
-/

namespace FoundationStoneTest16BB


abbrev StackReg := Fin 4
abbrev Reg5 := Fin 5

def stackReg (i : StackReg) : Reg5 := ⟨i.val, by omega⟩
def tempReg : Reg5 := 4

theorem stack_ne_temp (i : StackReg) : stackReg i ≠ tempReg := by
  intro h
  have := congrArg Fin.val h
  simp [stackReg, tempReg] at this
  omega

/-- Install the two active values into a five-counter background. -/
def install (i : StackReg) (base : Reg5 → Nat) (a b : Nat) : Reg5 → Nat :=
  fun j => if j = stackReg i then a else if j = tempReg then b else base j

theorem install_stack (i : StackReg) (base : Reg5 → Nat) (a b : Nat) :
    install i base a b (stackReg i) = a := by
  simp [install]

theorem install_temp (i : StackReg) (base : Reg5 → Nat) (a b : Nat) :
    install i base a b tempReg = b := by
  simp [install, (stack_ne_temp i).symm]

theorem install_other (i : StackReg) (base : Reg5 → Nat) (a b : Nat)
    (j : Reg5) (hji : j ≠ stackReg i) (hjt : j ≠ tempReg) :
    install i base a b j = base j := by
  simp [install, hji, hjt]

def activeReg (i : StackReg) : Bool → Reg5
  | false => stackReg i
  | true => tempReg

def embed (i : StackReg) (base : Reg5 → Nat) {L : Type}
    (pc : L) (a b : Nat) : FoundationStoneTest16AY.State 5 L :=
  ⟨pc, install i base a b⟩

@[simp] theorem embed_pc (i : StackReg) (base : Reg5 → Nat) {L : Type}
    (pc : L) (a b : Nat) : (embed i base pc a b).pc = pc := rfl

@[simp] theorem embed_change_pc (i : StackReg) (base : Reg5 → Nat) {L : Type}
    (pc next : L) (a b : Nat) :
    ({ embed i base pc a b with pc := next }) = embed i base next a b := rfl

@[simp] theorem embed_get (i : StackReg) (base : Reg5 → Nat) {L : Type}
    (pc : L) (a b : Nat) (body : Bool) :
    (embed i base pc a b).counters (activeReg i body) = if body then b else a := by
  cases body <;> simp [embed, activeReg, install_stack, install_temp]

@[simp] theorem embed_set (i : StackReg) (base : Reg5 → Nat) {L : Type}
    (pc next : L) (a b value : Nat) (body : Bool) :
    FoundationStoneTest16AY.setCounter (embed i base pc a b) next (activeReg i body) value =
      if body then embed i base next a value else embed i base next value b := by
  cases body
  · simp only [Bool.false_eq_true, ↓reduceIte]
    simp only [FoundationStoneTest16AY.setCounter, embed]
    apply congrArg (fun c => FoundationStoneTest16AY.State.mk next c)
    funext j
    by_cases hji : j = stackReg i
    · subst j; simp [activeReg, Function.update, install]
    · by_cases hjt : j = tempReg
      · subst j
        simp [activeReg, Function.update, install, (stack_ne_temp i).symm]
      · simp [activeReg, Function.update, install, hji, hjt]
  · simp only [↓reduceIte]
    simp only [FoundationStoneTest16AY.setCounter, embed]
    apply congrArg (fun c => FoundationStoneTest16AY.State.mk next c)
    funext j
    by_cases hjt : j = tempReg
    · subst j
      simp [activeReg, Function.update, install, (stack_ne_temp i).symm]
    · by_cases hji : j = stackReg i
      · subst j; simp [activeReg, Function.update, install, stack_ne_temp i]
      · simp [activeReg, Function.update, install, hji, hjt]

/-! ## Lift the 16AW multiplication and transfer programs -/

def liftAWInstr (i : StackReg) {L : Type} : FoundationStoneTest16AW.Instr L → FoundationStoneTest16AY.Instr 5 L
  | .inc body next => .inc (activeReg i body) next
  | .dec body positive zero => .dec (activeReg i body) positive zero
  | .halt => .halt

def liftAWProgram (i : StackReg) {L : Type} (P : L → FoundationStoneTest16AW.Instr L) :
    L → FoundationStoneTest16AY.Instr 5 L := fun l => liftAWInstr i (P l)

def embedAW (i : StackReg) (base : Reg5 → Nat) {L : Type}
    (s : FoundationStoneTest16AW.State L) : FoundationStoneTest16AY.State 5 L := embed i base s.pc s.a s.b

theorem step_lift_AW (i : StackReg) (base : Reg5 → Nat) {L : Type}
    (P : L → FoundationStoneTest16AW.Instr L) (s : FoundationStoneTest16AW.State L) :
    FoundationStoneTest16AY.step (liftAWProgram i P) (embedAW i base s) =
      (FoundationStoneTest16AW.step P s).map (embedAW i base) := by
  cases h : P s.pc with
  | halt => simp [FoundationStoneTest16AY.step, FoundationStoneTest16AW.step,
      liftAWProgram, embedAW, h, liftAWInstr]
  | inc body next =>
      cases body <;> simp [FoundationStoneTest16AY.step,
        FoundationStoneTest16AW.step, liftAWProgram, embedAW, h, liftAWInstr,
        FoundationStoneTest16AW.get, FoundationStoneTest16AW.set]
  | dec body positive zero =>
      cases body with
      | false =>
          by_cases hz : s.a = 0 <;> simp [FoundationStoneTest16AY.step,
            FoundationStoneTest16AW.step, liftAWProgram, embedAW, h, liftAWInstr,
            FoundationStoneTest16AW.get, FoundationStoneTest16AW.set, hz]
      | true =>
          by_cases hz : s.b = 0 <;> simp [FoundationStoneTest16AY.step,
            FoundationStoneTest16AW.step, liftAWProgram, embedAW, h, liftAWInstr,
            FoundationStoneTest16AW.get, FoundationStoneTest16AW.set, hz]

theorem run_lift_AW (i : StackReg) (base : Reg5 → Nat) {L : Type}
    (P : L → FoundationStoneTest16AW.Instr L) : ∀ n s,
    FoundationStoneTest16AY.run (liftAWProgram i P) n (embedAW i base s) =
      (FoundationStoneTest16AW.run P n s).map (embedAW i base) := by
  intro n
  induction n with
  | zero => intro s; rfl
  | succ n ih =>
      intro s
      unfold FoundationStoneTest16AY.run FoundationStoneTest16AW.run
      rw [step_lift_AW]
      cases hs : FoundationStoneTest16AW.step P s with
      | none => rfl
      | some s' => exact ih s'

theorem five_multiply_exact (i : StackReg) (base : Reg5 → Nat) (n : Nat) :
    FoundationStoneTest16AY.run (liftAWProgram i (FoundationStoneTest16AW.mulProgram 5)) (6 * n + 1)
        (embed i base FoundationStoneTest16AW.MLabel.loop n 0) =
      some (embed i base FoundationStoneTest16AW.MLabel.exit 0 (5 * n)) := by
  have h := run_lift_AW i base (FoundationStoneTest16AW.mulProgram 5)
    (6 * n + 1) (⟨FoundationStoneTest16AW.MLabel.loop, n, 0⟩)
  rw [FoundationStoneTest16AW.multiply_exact 5 n (by decide)] at h
  simpa [embedAW] using h

theorem five_transfer_exact (i : StackReg) (base : Reg5 → Nat) (n : Nat) :
    FoundationStoneTest16AY.run (liftAWProgram i FoundationStoneTest16AW.transferProgram) (2 * n + 1)
        (embed i base FoundationStoneTest16AW.TLabel.loop 0 n) =
      some (embed i base FoundationStoneTest16AW.TLabel.exit n 0) := by
  have h := run_lift_AW i base FoundationStoneTest16AW.transferProgram
    (2 * n + 1) (⟨FoundationStoneTest16AW.TLabel.loop, 0, n⟩)
  rw [FoundationStoneTest16AW.transfer_exact 0 n] at h
  simpa [embedAW] using h

/-! ## Lift the 16AV quotient/remainder program -/

def liftAVInstr (i : StackReg) : FoundationStoneTest16AV.Instr → FoundationStoneTest16AY.Instr 5 FoundationStoneTest16AV.Label
  | .inc body next => .inc (activeReg i body) next
  | .dec body positive zero => .dec (activeReg i body) positive zero
  | .halt => .halt

def liftAVProgram (i : StackReg) (P : FoundationStoneTest16AV.Label → FoundationStoneTest16AV.Instr) :
    FoundationStoneTest16AV.Label → FoundationStoneTest16AY.Instr 5 FoundationStoneTest16AV.Label := fun l => liftAVInstr i (P l)

def embedAV (i : StackReg) (base : Reg5 → Nat) (s : FoundationStoneTest16AV.State) :
    FoundationStoneTest16AY.State 5 FoundationStoneTest16AV.Label := embed i base s.pc s.a s.b

theorem step_lift_AV (i : StackReg) (base : Reg5 → Nat)
    (P : FoundationStoneTest16AV.Label → FoundationStoneTest16AV.Instr) (s : FoundationStoneTest16AV.State) :
    FoundationStoneTest16AY.step (liftAVProgram i P) (embedAV i base s) =
      (FoundationStoneTest16AV.step P s).map (embedAV i base) := by
  cases h : P s.pc with
  | halt => simp [FoundationStoneTest16AY.step, FoundationStoneTest16AV.step,
      liftAVProgram, embedAV, h, liftAVInstr]
  | inc body next =>
      cases body <;> simp [FoundationStoneTest16AY.step,
        FoundationStoneTest16AV.step, liftAVProgram, embedAV, h, liftAVInstr,
        FoundationStoneTest16AV.get, FoundationStoneTest16AV.set]
  | dec body positive zero =>
      cases body with
      | false =>
          by_cases hz : s.a = 0 <;> simp [FoundationStoneTest16AY.step,
            FoundationStoneTest16AV.step, liftAVProgram, embedAV, h, liftAVInstr,
            FoundationStoneTest16AV.get, FoundationStoneTest16AV.set, hz]
      | true =>
          by_cases hz : s.b = 0 <;> simp [FoundationStoneTest16AY.step,
            FoundationStoneTest16AV.step, liftAVProgram, embedAV, h, liftAVInstr,
            FoundationStoneTest16AV.get, FoundationStoneTest16AV.set, hz]

theorem run_lift_AV (i : StackReg) (base : Reg5 → Nat)
    (P : FoundationStoneTest16AV.Label → FoundationStoneTest16AV.Instr) : ∀ n s,
    FoundationStoneTest16AY.run (liftAVProgram i P) n (embedAV i base s) =
      (FoundationStoneTest16AV.run P n s).map (embedAV i base) := by
  intro n
  induction n with
  | zero => intro s; rfl
  | succ n ih =>
      intro s
      unfold FoundationStoneTest16AY.run FoundationStoneTest16AV.run
      rw [step_lift_AV]
      cases hs : FoundationStoneTest16AV.step P s with
      | none => rfl
      | some s' => exact ih s'

theorem five_divmod_exact (i : StackReg) (base : Reg5 → Nat) (n : Nat) :
    FoundationStoneTest16AY.run (liftAVProgram i (FoundationStoneTest16AV.divProgram 5))
        (6 * (n / 5) + (n % 5 + 1))
        (embed i base (FoundationStoneTest16AV.Label.scan 0) n 0) =
      some (embed i base (FoundationStoneTest16AV.Label.exit (n % 5)) 0 (n / 5)) := by
  have h := run_lift_AV i base (FoundationStoneTest16AV.divProgram 5)
    (6 * (n / 5) + (n % 5 + 1))
    (⟨FoundationStoneTest16AV.Label.scan 0, n, 0⟩)
  rw [FoundationStoneTest16AV.divmod_exact 5 n 0 (by decide)] at h
  simpa [embedAV] using h

/-! ## Preservation and restored-boundary statements -/

theorem multiply_boundary (i : StackReg) (base : Reg5 → Nat) (n : Nat) :
    let afterMul := embed i base FoundationStoneTest16AW.MLabel.exit 0 (5 * n)
    let afterRestore := embed i base FoundationStoneTest16AW.TLabel.exit (5 * n) 0
    afterMul.counters (stackReg i) = 0 ∧
    afterMul.counters tempReg = 5 * n ∧
    afterRestore.counters (stackReg i) = 5 * n ∧
    afterRestore.counters tempReg = 0 ∧
    ∀ j, j ≠ stackReg i → j ≠ tempReg →
      afterRestore.counters j = base j := by
  simp only [embed, install_stack, install_temp, true_and]
  intro j hji hjt
  exact install_other i base (5 * n) 0 j hji hjt

theorem division_boundary (i : StackReg) (base : Reg5 → Nat) (n : Nat) :
    let afterDiv := embed i base (FoundationStoneTest16AV.Label.exit (n % 5)) 0 (n / 5)
    let afterRestore := embed i base FoundationStoneTest16AW.TLabel.exit (n / 5) 0
    afterDiv.counters (stackReg i) = 0 ∧
    afterDiv.counters tempReg = n / 5 ∧
    afterRestore.counters (stackReg i) = n / 5 ∧
    afterRestore.counters tempReg = 0 ∧
    ∀ j, j ≠ stackReg i → j ≠ tempReg →
      afterRestore.counters j = base j := by
  simp only [embed, install_stack, install_temp, true_and]
  intro j hji hjt
  exact install_other i base (n / 5) 0 j hji hjt

theorem turing_chamber_16BB_certificate :
    (∀ (i : StackReg) base n,
      FoundationStoneTest16AY.run (liftAWProgram i (FoundationStoneTest16AW.mulProgram 5)) (6 * n + 1)
          (embed i base FoundationStoneTest16AW.MLabel.loop n 0) =
        some (embed i base FoundationStoneTest16AW.MLabel.exit 0 (5 * n))) ∧
    (∀ (i : StackReg) base n,
      FoundationStoneTest16AY.run (liftAVProgram i (FoundationStoneTest16AV.divProgram 5))
          (6 * (n / 5) + (n % 5 + 1))
          (embed i base (FoundationStoneTest16AV.Label.scan 0) n 0) =
        some (embed i base (FoundationStoneTest16AV.Label.exit (n % 5)) 0 (n / 5))) ∧
    (∀ (i : StackReg) base n,
      FoundationStoneTest16AY.run (liftAWProgram i FoundationStoneTest16AW.transferProgram) (2 * n + 1)
          (embed i base FoundationStoneTest16AW.TLabel.loop 0 n) =
        some (embed i base FoundationStoneTest16AW.TLabel.exit n 0)) ∧
    (∀ (i : StackReg) base n,
      (embed i base FoundationStoneTest16AW.TLabel.exit n 0).counters tempReg = 0) :=
  ⟨five_multiply_exact, five_divmod_exact, five_transfer_exact,
   fun i base n => by simp [embed, install_temp]⟩

#print axioms step_lift_AW
#print axioms run_lift_AW
#print axioms five_multiply_exact
#print axioms five_divmod_exact
#print axioms five_transfer_exact
#print axioms multiply_boundary
#print axioms division_boundary
#print axioms turing_chamber_16BB_certificate

end FoundationStoneTest16BB
