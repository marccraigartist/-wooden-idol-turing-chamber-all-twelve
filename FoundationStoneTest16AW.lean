import Mathlib

/-!
# THE TURING CHAMBER — TEST 16AW: PARAMETRIC PRIMITIVE MULTIPLY AND RESTORE

Lean 4.35.0-rc2 / pinned Mathlib.

Together with 16AV's division gate, these are the primitive two-counter blocks
needed by prime-exponent packing.  `mulProgram p` consumes A and produces
`p*A` in initially-zero B.  `transferProgram` then moves B back into A.
Every transition is increment or zero-test/decrement-and-branch.
-/

namespace FoundationStoneTest16AW

abbrev Body := Bool

inductive MLabel
  | loop
  | add (remaining : Nat)
  | exit
deriving DecidableEq, Repr

inductive TLabel
  | loop
  | credit
  | exit
deriving DecidableEq, Repr

inductive Instr (L : Type)
  | inc (body : Body) (next : L)
  | dec (body : Body) (positive zero : L)
  | halt

structure State (L : Type) where
  pc : L
  a : Nat
  b : Nat
deriving DecidableEq, Repr

def get {L : Type} (s : State L) (body : Body) : Nat := if body then s.b else s.a

def set {L : Type} (s : State L) (pc : L) (body : Body) (value : Nat) : State L :=
  if body then ⟨pc, s.a, value⟩ else ⟨pc, value, s.b⟩

def step {L : Type} (P : L → Instr L) (s : State L) : Option (State L) :=
  match P s.pc with
  | .halt => none
  | .inc body next => some (set s next body (get s body + 1))
  | .dec body positive zero =>
      if get s body = 0 then some { s with pc := zero }
      else some (set s positive body (get s body - 1))

def run {L : Type} (P : L → Instr L) : Nat → State L → Option (State L)
  | 0, s => some s
  | n + 1, s =>
      match step P s with
      | none => none
      | some s' => run P n s'

theorem run_add {L : Type} (P : L → Instr L) (m : Nat) : ∀ n s,
    run P (m + n) s =
      match run P m s with
      | none => none
      | some s' => run P n s' := by
  intro n
  induction m with
  | zero => intro s; simp [run]
  | succ m ih =>
      intro s
      simp only [Nat.succ_add, run]
      cases step P s with
      | none => rfl
      | some s' => exact ih s'

def mulProgram (p : Nat) : MLabel → Instr MLabel
  | .loop => .dec false (.add p) .exit
  | .add 0 => .halt
  | .add (d + 1) => .inc true (if d = 0 then .loop else .add d)
  | .exit => .halt

theorem add_steps : ∀ d a b, 0 < d →
    run (mulProgram p) d ⟨MLabel.add d, a, b⟩ =
      some ⟨MLabel.loop, a, b + d⟩ := by
  intro d
  induction d with
  | zero => intro a b h; omega
  | succ d ih =>
      intro a b _
      by_cases hz : d = 0
      · subst d
        simp [run, step, mulProgram, get, set]
      · simp only [run]
        simp [step, mulProgram, get, set, hz]
        rw [ih a (b + 1) (by omega)]
        congr 2
        omega

theorem mul_cycle (p a b : Nat) (hp : 0 < p) (ha : 0 < a) :
    run (mulProgram p) (p + 1) ⟨MLabel.loop, a, b⟩ =
      some ⟨MLabel.loop, a - 1, b + p⟩ := by
  rw [show p + 1 = 1 + p by omega, run_add]
  simp [run, step, mulProgram, get, set, ha.ne']
  exact add_steps p (a - 1) b hp

theorem mul_groups (p n b : Nat) (hp : 0 < p) :
    run (mulProgram p) ((p + 1) * n) ⟨MLabel.loop, n, b⟩ =
      some ⟨MLabel.loop, 0, b + p * n⟩ := by
  induction n generalizing b with
  | zero => simp [run]
  | succ n ih =>
      rw [show (p + 1) * (n + 1) = (p + 1) + (p + 1) * n by ring,
        run_add, mul_cycle p (n + 1) b hp (by omega)]
      simp only [Nat.add_sub_cancel]
      rw [ih (b + p)]
      congr 2
      ring

theorem mul_terminal (p b : Nat) :
    run (mulProgram p) 1 ⟨MLabel.loop, 0, b⟩ =
      some ⟨MLabel.exit, 0, b⟩ := by
  simp [run, step, mulProgram, get, set]

theorem multiply_exact (p n : Nat) (hp : 0 < p) :
    run (mulProgram p) ((p + 1) * n + 1) ⟨MLabel.loop, n, 0⟩ =
      some ⟨MLabel.exit, 0, p * n⟩ := by
  rw [run_add, mul_groups p n 0 hp]
  simpa using mul_terminal p (p * n)

def transferProgram : TLabel → Instr TLabel
  | .loop => .dec true .credit .exit
  | .credit => .inc false .loop
  | .exit => .halt

theorem transfer_cycle (a b : Nat) (hb : 0 < b) :
    run transferProgram 2 ⟨TLabel.loop, a, b⟩ =
      some ⟨TLabel.loop, a + 1, b - 1⟩ := by
  simp [run, step, transferProgram, get, set, hb.ne']

theorem transfer_groups (a n : Nat) :
    run transferProgram (2 * n) ⟨TLabel.loop, a, n⟩ =
      some ⟨TLabel.loop, a + n, 0⟩ := by
  induction n generalizing a with
  | zero => simp [run]
  | succ n ih =>
      rw [show 2 * (n + 1) = 2 + 2 * n by omega,
        run_add, transfer_cycle a (n + 1) (by omega)]
      simp only [Nat.add_sub_cancel]
      rw [ih (a + 1)]
      congr 2
      omega

theorem transfer_terminal (a : Nat) :
    run transferProgram 1 ⟨TLabel.loop, a, 0⟩ =
      some ⟨TLabel.exit, a, 0⟩ := by
  simp [run, step, transferProgram, get, set]

theorem transfer_exact (a n : Nat) :
    run transferProgram (2 * n + 1) ⟨TLabel.loop, a, n⟩ =
      some ⟨TLabel.exit, a + n, 0⟩ := by
  rw [run_add, transfer_groups]
  simpa using transfer_terminal (a + n)

/-- Sequential block contract used for multiplying packed A by a prime and
restoring zero scratch. -/
theorem multiply_then_restore (p n : Nat) (hp : 0 < p) :
    run (mulProgram p) ((p + 1) * n + 1) ⟨MLabel.loop, n, 0⟩ =
        some ⟨MLabel.exit, 0, p * n⟩ ∧
    run transferProgram (2 * (p * n) + 1) ⟨TLabel.loop, 0, p * n⟩ =
        some ⟨TLabel.exit, p * n, 0⟩ :=
  ⟨multiply_exact p n hp, by simpa using transfer_exact 0 (p * n)⟩

/-! Red control: multiplication without restoration leaves the packed value in
the scratch counter, not in the represented-state counter. -/

theorem multiply_alone_wrong_register :
    (⟨MLabel.exit, 0, 6⟩ : State MLabel).a ≠ 6 := by decide

theorem turing_chamber_16AW_certificate (p n : Nat) (hp : 0 < p) :
    run (mulProgram p) ((p + 1) * n + 1) ⟨MLabel.loop, n, 0⟩ =
        some ⟨MLabel.exit, 0, p * n⟩ ∧
    run transferProgram (2 * (p * n) + 1) ⟨TLabel.loop, 0, p * n⟩ =
        some ⟨TLabel.exit, p * n, 0⟩ ∧
    (⟨MLabel.exit, 0, 6⟩ : State MLabel).a ≠ 6 :=
  ⟨multiply_exact p n hp, by simpa using transfer_exact 0 (p * n),
   multiply_alone_wrong_register⟩

#print axioms add_steps
#print axioms multiply_exact
#print axioms transfer_exact
#print axioms multiply_then_restore
#print axioms turing_chamber_16AW_certificate

end FoundationStoneTest16AW
