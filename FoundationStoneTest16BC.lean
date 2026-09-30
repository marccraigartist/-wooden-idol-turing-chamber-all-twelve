import FoundationStoneTest16BB

/-!
# THE TURING CHAMBER — TEST 16BC: THE ARITHMETIC CORES ARE FINITE

Lean 4.35.0-rc2 / pinned Mathlib.

Tests 16AV and 16AW proved the arithmetic, but used convenient `Nat`-indexed
labels.  Only finitely many of those labels are reachable when the stack base
is five.  A compiler to a finite program must remove the unreachable infinity,
not merely promise never to visit it.

This file constructs the exact finite controls:

* multiplication by five: 7 labels (`loop`, five additions, `exit`);
* division by five: 12 labels (five scans, `credit`, five remainder exits,
  `bad`);
* scratch transfer: 3 labels.

Each finite program is related step-for-step to the already verified program.
The exact running-time and arithmetic theorems therefore transfer without a
new arithmetic assumption.  Red controls exhibit old labels which deliberately
have no finite preimage.

Scope: this closes the finite-control leak in the arithmetic cores.  Patching
their exits into complete push/pop/peek instruction blocks remains the next
linker construction; it is not assumed here.
-/

namespace FoundationStoneTest16BC

/-! ## A generic relabelling lemma for 16AW machines -/

def mapInstr {L K : Type} (f : L → K) : FoundationStoneTest16AW.Instr L → FoundationStoneTest16AW.Instr K
  | .inc body next => .inc body (f next)
  | .dec body positive zero => .dec body (f positive) (f zero)
  | .halt => .halt

def mapState {L K : Type} (f : L → K) (s : FoundationStoneTest16AW.State L) : FoundationStoneTest16AW.State K :=
  ⟨f s.pc, s.a, s.b⟩

theorem mapState_injective {L K : Type} (f : L → K) (hf : Function.Injective f) :
    Function.Injective (mapState f) := by
  intro s t h
  cases s with
  | mk sp sa sb =>
    cases t with
    | mk tp ta tb =>
      simp only [mapState, FoundationStoneTest16AW.State.mk.injEq] at h ⊢
      exact ⟨hf h.1, h.2.1, h.2.2⟩

theorem step_relabels {L K : Type} (f : L → K)
    (P : L → FoundationStoneTest16AW.Instr L) (Q : K → FoundationStoneTest16AW.Instr K)
    (hPQ : ∀ l, Q (f l) = mapInstr f (P l)) (s : FoundationStoneTest16AW.State L) :
    FoundationStoneTest16AW.step Q (mapState f s) = (FoundationStoneTest16AW.step P s).map (mapState f) := by
  cases s with
  | mk pc a b =>
    change FoundationStoneTest16AW.step Q ⟨f pc, a, b⟩ = _
    unfold FoundationStoneTest16AW.step
    rw [hPQ pc]
    cases h : P pc with
    | halt => simp [FoundationStoneTest16AW.step, h, mapInstr, mapState]
    | inc body next =>
      cases body <;> simp [FoundationStoneTest16AW.step, h, mapInstr, mapState, FoundationStoneTest16AW.get, FoundationStoneTest16AW.set]
    | dec body positive zero =>
      cases body with
      | false =>
          by_cases hz : a = 0 <;>
            simp [FoundationStoneTest16AW.step, h, mapInstr, mapState, FoundationStoneTest16AW.get, FoundationStoneTest16AW.set, hz]
      | true =>
          by_cases hz : b = 0 <;>
            simp [FoundationStoneTest16AW.step, h, mapInstr, mapState, FoundationStoneTest16AW.get, FoundationStoneTest16AW.set, hz]

theorem run_relabels {L K : Type} (f : L → K)
    (P : L → FoundationStoneTest16AW.Instr L) (Q : K → FoundationStoneTest16AW.Instr K)
    (hPQ : ∀ l, Q (f l) = mapInstr f (P l)) : ∀ n s,
    FoundationStoneTest16AW.run Q n (mapState f s) = (FoundationStoneTest16AW.run P n s).map (mapState f) := by
  intro n
  induction n with
  | zero => intro s; rfl
  | succ n ih =>
      intro s
      unfold FoundationStoneTest16AW.run
      rw [step_relabels f P Q hPQ]
      cases hs : FoundationStoneTest16AW.step P s with
      | none => rfl
      | some s' => exact ih s'

/-! ## The seven-label multiplier -/

inductive M5
  | loop
  | add (slot : Fin 5)
  | exit
deriving DecidableEq, Repr, Fintype

def M5.toOld : M5 → FoundationStoneTest16AW.MLabel
  | .loop => .loop
  | .add slot => .add (slot.val + 1)
  | .exit => .exit

theorem M5.toOld_injective : Function.Injective M5.toOld := by
  intro x y h
  cases x <;> cases y <;> simp_all [M5.toOld]
  apply Fin.ext
  omega

def mul5 : M5 → FoundationStoneTest16AW.Instr M5
  | .loop => .dec false (.add 4) .exit
  | .add slot =>
      if h : slot.val = 0 then .inc true .loop
      else .inc true (.add ⟨slot.val - 1, by omega⟩)
  | .exit => .halt

theorem mul5_matches_old : ∀ l, FoundationStoneTest16AW.mulProgram 5 (M5.toOld l) = mapInstr M5.toOld (mul5 l) := by
  intro l
  cases l with
  | loop => rfl
  | exit => rfl
  | add slot => fin_cases slot <;> rfl

theorem mul5_exact (n : Nat) :
    FoundationStoneTest16AW.run mul5 (6 * n + 1) ⟨M5.loop, n, 0⟩ =
      some ⟨M5.exit, 0, 5 * n⟩ := by
  have h := run_relabels M5.toOld mul5 (FoundationStoneTest16AW.mulProgram 5) mul5_matches_old
    (6 * n + 1) (⟨M5.loop, n, 0⟩ : FoundationStoneTest16AW.State M5)
  simp only [mapState, M5.toOld] at h
  have hold := FoundationStoneTest16AW.multiply_exact 5 n (by decide)
  norm_num at hold
  rw [hold] at h
  cases hr : FoundationStoneTest16AW.run mul5 (6 * n + 1) (⟨M5.loop, n, 0⟩ : FoundationStoneTest16AW.State M5) with
  | none => simp [hr] at h
  | some t =>
      rw [hr] at h
      simp only [Option.map, Option.some.injEq] at h
      have ht : t = (⟨M5.exit, 0, 5 * n⟩ : FoundationStoneTest16AW.State M5) :=
        mapState_injective M5.toOld M5.toOld_injective h.symm
      simpa [hr, ht]

/-! ## The twelve-label divider -/

inductive D5
  | scan (slot : Fin 5)
  | credit
  | exit (remainder : Fin 5)
  | bad
deriving DecidableEq, Repr, Fintype

def D5.toOld : D5 → FoundationStoneTest16AV.Label
  | .scan slot => .scan slot.val
  | .credit => .credit
  | .exit remainder => .exit remainder.val
  | .bad => .bad

theorem D5.toOld_injective : Function.Injective D5.toOld := by
  intro x y h
  cases x <;> cases y <;> simp_all [D5.toOld]
  all_goals apply Fin.ext <;> assumption

def div5 : D5 → FoundationStoneTest16AW.Instr D5
  | .scan slot =>
      if h : slot.val < 4 then
        .dec false (.scan ⟨slot.val + 1, by omega⟩) (.exit slot)
      else .dec false .credit (.exit slot)
  | .credit => .inc true (.scan 0)
  | .exit _ => .halt
  | .bad => .halt

def toAVInstr {L : Type} (f : L → FoundationStoneTest16AV.Label) : FoundationStoneTest16AW.Instr L → FoundationStoneTest16AV.Instr
  | .inc body next => .inc body (f next)
  | .dec body positive zero => .dec body (f positive) (f zero)
  | .halt => .halt

def mapStateAV {L : Type} (f : L → FoundationStoneTest16AV.Label) (s : FoundationStoneTest16AW.State L) : FoundationStoneTest16AV.State :=
  ⟨f s.pc, s.a, s.b⟩

theorem mapStateAV_injective {L : Type} (f : L → FoundationStoneTest16AV.Label) (hf : Function.Injective f) :
    Function.Injective (mapStateAV f) := by
  intro s t h
  cases s with
  | mk sp sa sb =>
    cases t with
    | mk tp ta tb =>
      have hp : sp = tp := hf (congrArg FoundationStoneTest16AV.State.pc h)
      have ha : sa = ta := congrArg FoundationStoneTest16AV.State.a h
      have hb : sb = tb := congrArg FoundationStoneTest16AV.State.b h
      subst tp; subst ta; subst tb; rfl

theorem div5_matches_old : ∀ l,
    FoundationStoneTest16AV.divProgram 5 (D5.toOld l) = toAVInstr D5.toOld (div5 l) := by
  intro l
  cases l with
  | credit => rfl
  | bad => rfl
  | exit r => rfl
  | scan slot => fin_cases slot <;> rfl

theorem step_relabels_AV {L : Type} (f : L → FoundationStoneTest16AV.Label)
    (P : L → FoundationStoneTest16AW.Instr L) (Q : FoundationStoneTest16AV.Label → FoundationStoneTest16AV.Instr)
    (hPQ : ∀ l, Q (f l) = toAVInstr f (P l)) (s : FoundationStoneTest16AW.State L) :
    FoundationStoneTest16AV.step Q (mapStateAV f s) = (FoundationStoneTest16AW.step P s).map (mapStateAV f) := by
  cases s with
  | mk pc a b =>
    change FoundationStoneTest16AV.step Q ⟨f pc, a, b⟩ = _
    unfold FoundationStoneTest16AV.step
    rw [hPQ pc]
    cases h : P pc with
    | halt => simp [FoundationStoneTest16AV.step, FoundationStoneTest16AW.step, h, toAVInstr, mapStateAV]
    | inc body next =>
      cases body <;> simp [FoundationStoneTest16AV.step, FoundationStoneTest16AW.step, h, toAVInstr, mapStateAV,
        FoundationStoneTest16AV.get, FoundationStoneTest16AV.set, FoundationStoneTest16AW.get, FoundationStoneTest16AW.set]
    | dec body positive zero =>
      cases body with
      | false =>
          by_cases hz : a = 0 <;>
            simp [FoundationStoneTest16AV.step, FoundationStoneTest16AW.step, h, toAVInstr, mapStateAV,
              FoundationStoneTest16AV.get, FoundationStoneTest16AV.set, FoundationStoneTest16AW.get, FoundationStoneTest16AW.set, hz]
      | true =>
          by_cases hz : b = 0 <;>
            simp [FoundationStoneTest16AV.step, FoundationStoneTest16AW.step, h, toAVInstr, mapStateAV,
              FoundationStoneTest16AV.get, FoundationStoneTest16AV.set, FoundationStoneTest16AW.get, FoundationStoneTest16AW.set, hz]

theorem run_relabels_AV {L : Type} (f : L → FoundationStoneTest16AV.Label)
    (P : L → FoundationStoneTest16AW.Instr L) (Q : FoundationStoneTest16AV.Label → FoundationStoneTest16AV.Instr)
    (hPQ : ∀ l, Q (f l) = toAVInstr f (P l)) : ∀ n s,
    FoundationStoneTest16AV.run Q n (mapStateAV f s) = (FoundationStoneTest16AW.run P n s).map (mapStateAV f) := by
  intro n
  induction n with
  | zero => intro s; rfl
  | succ n ih =>
      intro s
      unfold FoundationStoneTest16AV.run FoundationStoneTest16AW.run
      rw [step_relabels_AV f P Q hPQ]
      cases hs : FoundationStoneTest16AW.step P s with
      | none => rfl
      | some s' => exact ih s'

theorem div5_exact (n : Nat) :
    FoundationStoneTest16AW.run div5 (6 * (n / 5) + (n % 5 + 1)) ⟨D5.scan 0, n, 0⟩ =
      some ⟨D5.exit ⟨n % 5, Nat.mod_lt n (by decide)⟩, 0, n / 5⟩ := by
  let r : Fin 5 := ⟨n % 5, Nat.mod_lt n (by decide)⟩
  have h := run_relabels_AV D5.toOld div5 (FoundationStoneTest16AV.divProgram 5) div5_matches_old
    (6 * (n / 5) + (n % 5 + 1)) (⟨D5.scan 0, n, 0⟩ : FoundationStoneTest16AW.State D5)
  simp only [mapStateAV, D5.toOld] at h
  have hold := FoundationStoneTest16AV.divmod_exact 5 n 0 (by decide)
  norm_num at hold
  have hold' :
      FoundationStoneTest16AV.run (FoundationStoneTest16AV.divProgram 5)
          (6 * (n / 5) + (n % 5 + 1))
          ⟨FoundationStoneTest16AV.Label.scan ((0 : Fin 5).val), n, 0⟩ =
        some ⟨FoundationStoneTest16AV.Label.exit (n % 5), 0, n / 5⟩ := by
    simpa using hold
  rw [hold'] at h
  cases hr : FoundationStoneTest16AW.run div5 (6 * (n / 5) + (n % 5 + 1))
      (⟨D5.scan 0, n, 0⟩ : FoundationStoneTest16AW.State D5) with
  | none => simp [hr] at h
  | some t =>
      rw [hr] at h
      simp only [Option.map, Option.some.injEq, Nat.zero_add] at h
      have hm : mapStateAV D5.toOld
          (⟨D5.exit r, 0, n / 5⟩ : FoundationStoneTest16AW.State D5) =
          (⟨FoundationStoneTest16AV.Label.exit (n % 5), 0, n / 5⟩ : FoundationStoneTest16AV.State) := by
        simp [mapStateAV, D5.toOld, r]
      have ht : t = (⟨D5.exit r, 0, n / 5⟩ : FoundationStoneTest16AW.State D5) := by
        apply mapStateAV_injective D5.toOld D5.toOld_injective
        rw [hm]
        exact h.symm
      simpa [hr, ht, r]

/-! ## The three-label transfer -/

abbrev T3 := Fin 3

namespace T3
def loop : T3 := 0
def credit : T3 := 1
def exit : T3 := 2
end T3

def T3.toOld (l : T3) : FoundationStoneTest16AW.TLabel :=
  if l = T3.loop then .loop else if l = T3.credit then .credit else .exit

theorem T3.toOld_injective : Function.Injective T3.toOld := by
  intro x y
  fin_cases x <;> fin_cases y <;> simp [T3.toOld, T3.loop, T3.credit]

def transfer3 (l : T3) : FoundationStoneTest16AW.Instr T3 :=
  if l = T3.loop then .dec true T3.credit T3.exit
  else if l = T3.credit then .inc false T3.loop
  else .halt

theorem transfer3_matches_old : ∀ l,
    FoundationStoneTest16AW.transferProgram (T3.toOld l) = mapInstr T3.toOld (transfer3 l) := by
  intro l; fin_cases l <;> rfl

theorem transfer3_exact (a n : Nat) :
    FoundationStoneTest16AW.run transfer3 (2 * n + 1) ⟨T3.loop, a, n⟩ =
      some ⟨T3.exit, a + n, 0⟩ := by
  have h := run_relabels T3.toOld transfer3 FoundationStoneTest16AW.transferProgram transfer3_matches_old
    (2 * n + 1) (⟨T3.loop, a, n⟩ : FoundationStoneTest16AW.State T3)
  change FoundationStoneTest16AW.run FoundationStoneTest16AW.transferProgram (2 * n + 1)
      ⟨FoundationStoneTest16AW.TLabel.loop, a, n⟩ = _ at h
  rw [FoundationStoneTest16AW.transfer_exact a n] at h
  cases hr : FoundationStoneTest16AW.run transfer3 (2 * n + 1) (⟨T3.loop, a, n⟩ : FoundationStoneTest16AW.State T3) with
  | none => simp [hr] at h
  | some t =>
      rw [hr] at h
      simp only [Option.map, Option.some.injEq] at h
      have ht : t = (⟨T3.exit, a + n, 0⟩ : FoundationStoneTest16AW.State T3) :=
        mapState_injective T3.toOld T3.toOld_injective h.symm
      simpa [hr, ht]

/-! ## Cardinalities and red controls -/

theorem finite_control_sizes :
    Fintype.card M5 = 7 ∧ Fintype.card D5 = 12 ∧ Fintype.card T3 = 3 := by
  decide

theorem old_add_six_has_no_finite_name : ¬ ∃ l : M5, M5.toOld l = .add 6 := by
  intro h
  obtain ⟨l, hl⟩ := h
  cases l with
  | loop => simp [M5.toOld] at hl
  | exit => simp [M5.toOld] at hl
  | add slot => fin_cases slot <;> simp [M5.toOld] at hl

theorem old_scan_five_has_no_finite_name : ¬ ∃ l : D5, D5.toOld l = .scan 5 := by
  intro h
  obtain ⟨l, hl⟩ := h
  cases l with
  | credit => simp [D5.toOld] at hl
  | bad => simp [D5.toOld] at hl
  | exit r => simp [D5.toOld] at hl
  | scan slot => fin_cases slot <;> simp [D5.toOld] at hl

theorem turing_chamber_16BC_certificate :
    (Fintype.card M5 = 7 ∧ Fintype.card D5 = 12 ∧ Fintype.card T3 = 3) ∧
    (∀ n, FoundationStoneTest16AW.run mul5 (6 * n + 1) ⟨M5.loop, n, 0⟩ =
      some ⟨M5.exit, 0, 5 * n⟩) ∧
    (∀ n, FoundationStoneTest16AW.run div5 (6 * (n / 5) + (n % 5 + 1)) ⟨D5.scan 0, n, 0⟩ =
      some ⟨D5.exit ⟨n % 5, Nat.mod_lt n (by decide)⟩, 0, n / 5⟩) ∧
    (∀ a n, FoundationStoneTest16AW.run transfer3 (2 * n + 1) ⟨T3.loop, a, n⟩ =
      some ⟨T3.exit, a + n, 0⟩) ∧
    (¬ ∃ l : M5, M5.toOld l = .add 6) ∧
    (¬ ∃ l : D5, D5.toOld l = .scan 5) :=
  ⟨finite_control_sizes, mul5_exact, div5_exact, transfer3_exact,
   old_add_six_has_no_finite_name, old_scan_five_has_no_finite_name⟩

#print axioms mul5_exact
#print axioms div5_exact
#print axioms transfer3_exact
#print axioms turing_chamber_16BC_certificate

end FoundationStoneTest16BC
