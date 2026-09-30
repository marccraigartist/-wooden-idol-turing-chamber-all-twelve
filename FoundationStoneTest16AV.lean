import Mathlib

/-!
# THE TURING CHAMBER — TEST 16AV: PARAMETRIC PRIMITIVE DIVISION

Lean 4.35.0-rc2 / pinned Mathlib.

Unlike 16AS, every transition here is a primitive two-counter instruction:
increment one counter, or zero-test/decrement one counter and branch.  For any
positive `p`, `divProgram p` removes A one token at a time, counts complete
groups in B, and exits through a label carrying the remainder.

Lean certifies the exact quotient, remainder and running time.  The earlier
literal programs for p=2 and p=5 are finite numeric-label presentations of
this same structured gate.
-/

namespace FoundationStoneTest16AV

abbrev Body := Bool

inductive Label
  | scan (i : Nat)
  | credit
  | exit (r : Nat)
  | bad
deriving DecidableEq, Repr

inductive Instr
  | inc (body : Body) (next : Label)
  | dec (body : Body) (positive zero : Label)
  | halt
deriving DecidableEq, Repr

structure State where
  pc : Label
  a : Nat
  b : Nat
deriving DecidableEq, Repr

def get (s : State) (body : Body) : Nat := if body then s.b else s.a

def set (s : State) (pc : Label) (body : Body) (value : Nat) : State :=
  if body then ⟨pc, s.a, value⟩ else ⟨pc, value, s.b⟩

/-- One scan site per possible residue.  Invalid sites halt. -/
def divProgram (p : Nat) : Label → Instr
  | .scan i =>
      if i + 1 < p then .dec false (.scan (i + 1)) (.exit i)
      else if i + 1 = p then .dec false .credit (.exit i)
      else .halt
  | .credit => .inc true (.scan 0)
  | .exit _ => .halt
  | .bad => .halt

def step (P : Label → Instr) (s : State) : Option State :=
  match P s.pc with
  | .halt => none
  | .inc body next => some (set s next body (get s body + 1))
  | .dec body positive zero =>
      if get s body = 0 then some { s with pc := zero }
      else some (set s positive body (get s body - 1))

def run (P : Label → Instr) : Nat → State → Option State
  | 0, s => some s
  | n + 1, s =>
      match step P s with
      | none => none
      | some s' => run P n s'

theorem run_add (P : Label → Instr) (m : Nat) : ∀ n s,
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

/-- Consume `d` tokens without completing a group. -/
theorem scan_prefix (p : Nat) : ∀ d i a b,
    i + d < p → d ≤ a →
    run (divProgram p) d ⟨.scan i, a, b⟩ =
      some ⟨.scan (i + d), a - d, b⟩ := by
  intro d
  induction d with
  | zero => intro i a b _ _; simp [run]
  | succ d ih =>
      intro i a b hip hda
      have hi : i + 1 < p := by omega
      have ha : a ≠ 0 := by omega
      rw [show d + 1 = 1 + d by omega, run_add]
      simp [run, step, divProgram, hi, get, set, ha]
      have hrec := ih (i + 1) (a - 1) b (by omega) (by omega)
      rw [hrec]
      congr 2
      · congr 1
        omega
      · rw [Nat.sub_sub]

/-- Consume the remaining `d>0` tokens of one complete group and arrive at
the credit instruction. -/
theorem scan_to_credit (p : Nat) : ∀ d i a b,
    0 < d → i + d = p → d ≤ a →
    run (divProgram p) d ⟨.scan i, a, b⟩ =
      some ⟨.credit, a - d, b⟩ := by
  intro d
  induction d with
  | zero => intro i a b hd _ _; omega
  | succ d ih =>
      intro i a b hd hip hda
      by_cases hz : d = 0
      · subst d
        have heq : i + 1 = p := by omega
        have hnlt : ¬ i + 1 < p := by omega
        have ha : a ≠ 0 := by omega
        simp [run, step, divProgram, hnlt, heq, get, set, ha]
      · have hi : i + 1 < p := by omega
        have ha : a ≠ 0 := by omega
        rw [show d + 1 = 1 + d by omega, run_add]
        simp [run, step, divProgram, hi, get, set, ha]
        have hrec := ih (i + 1) (a - 1) b (by omega) (by omega) (by omega)
        rw [hrec]
        congr 2 <;> omega

theorem one_group (p a b : Nat) (hp : 0 < p) (ha : p ≤ a) :
    run (divProgram p) (p + 1) ⟨.scan 0, a, b⟩ =
      some ⟨.scan 0, a - p, b + 1⟩ := by
  rw [run_add]
  rw [scan_to_credit p p 0 a b hp (by omega) ha]
  simp [run, step, divProgram, get, set]

theorem complete_groups (p q r b : Nat) (hp : 0 < p) :
    run (divProgram p) ((p + 1) * q) ⟨.scan 0, p * q + r, b⟩ =
      some ⟨.scan 0, r, b + q⟩ := by
  induction q generalizing r b with
  | zero => simp [run]
  | succ q ih =>
      have ha : p * (q + 1) + r = p * q + (p + r) := by
        simp [Nat.mul_succ, Nat.add_assoc, Nat.add_comm p r]
      rw [ha, Nat.mul_succ, run_add, ih (p + r) b]
      simp only
      rw [one_group]
      · simp only [Nat.add_sub_cancel_left]
        congr 2
      · exact hp
      · omega

theorem remainder_exit (p r b : Nat) (hr : r < p) :
    run (divProgram p) (r + 1) ⟨.scan 0, r, b⟩ =
      some ⟨.exit r, 0, b⟩ := by
  rw [run_add]
  have hpre := scan_prefix p r 0 r b (by omega) (by omega)
  simp only [Nat.zero_add, Nat.sub_self] at hpre
  rw [hpre]
  by_cases hlt : r + 1 < p
  · simp [run, step, divProgram, hlt, get, set]
  · have heq : r + 1 = p := by omega
    simp [run, step, divProgram, hlt, heq, get, set]

/-- Full primitive-machine quotient/remainder theorem. -/
theorem divmod_exact (p n b : Nat) (hp : 0 < p) :
    run (divProgram p) ((p + 1) * (n / p) + (n % p + 1))
        ⟨.scan 0, n, b⟩ =
      some ⟨.exit (n % p), 0, b + n / p⟩ := by
  rw [run_add]
  have hn : p * (n / p) + n % p = n := by
    simpa [Nat.mul_comm] using Nat.div_add_mod n p
  have hg := complete_groups p (n / p) (n % p) b hp
  rw [hn] at hg
  rw [hg]
  exact remainder_exit p (n % p) (b + n / p) (Nat.mod_lt _ hp)

theorem halt_after_exit (p r b : Nat) :
    step (divProgram p) ⟨.exit r, 0, b⟩ = none := rfl

/-! Red control: removing the zero branch makes all remainders indistinguishable. -/

def brokenProgram (p : Nat) : Label → Instr
  | .scan i => .dec false (.scan ((i + 1) % p)) .bad
  | .credit => .inc true (.scan 0)
  | _ => .halt

theorem broken_zero_branch_forgets_remainder (p r b : Nat) :
    step (brokenProgram p) ⟨.scan r, 0, b⟩ = some ⟨.bad, 0, b⟩ := by
  simp [step, brokenProgram, get]

theorem turing_chamber_16AV_certificate (p n b : Nat) (hp : 0 < p) :
    run (divProgram p) ((p + 1) * (n / p) + (n % p + 1))
        ⟨.scan 0, n, b⟩ =
      some ⟨.exit (n % p), 0, b + n / p⟩ ∧
    step (divProgram p) ⟨.exit (n % p), 0, b + n / p⟩ = none ∧
    step (brokenProgram p) ⟨.scan (n % p), 0, b⟩ = some ⟨.bad, 0, b⟩ :=
  ⟨divmod_exact p n b hp, halt_after_exit p _ _,
   broken_zero_branch_forgets_remainder p _ _⟩

#print axioms scan_prefix
#print axioms scan_to_credit
#print axioms divmod_exact
#print axioms turing_chamber_16AV_certificate

end FoundationStoneTest16AV
