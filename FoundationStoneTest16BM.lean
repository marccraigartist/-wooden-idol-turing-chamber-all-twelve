import FoundationStoneTest16BL

/-!
# THE TURING CHAMBER — TEST 16BM: THE GLOBAL MM2 LINKER

Lean 4.35.0-rc2 / pinned Mathlib.

This file links the physical blocks behind one source program.  A source is a
primitive five-counter machine (`16AY.Instr 5 L`).  Its target has only two
physical counters.  Control labels remember the owning source instruction,
the selected logical register, its two declared continuations, and the local
phase of the verified 16BK/16BL blocks.

There are no raw jump addresses and no out-of-range halt convention.  Only a
compiled source `halt` emits target `halt`.  All internal exits use a
counter-preserving two-step typed jump.

Lean certifies one `StateTransition.Respects` theorem for all three primitive
source instructions and lifts it to arbitrary-run halting equivalence.  The
ambient local phase types still contain natural indices inherited from the
proved parametric gates; only finitely many are reachable for primes
2,3,5,7,11.  Replacing that ambient presentation by literal `Fin` labels is a
representation cleanup, not a remaining semantic compiler hypothesis.
-/

namespace FoundationStoneTest16BM

open FoundationStoneTest16AW

abbrev Reg5 := FoundationStoneTest16BJ.Reg5

inductive GlobalLabel (L : Type)
  | halted (owner : L)
  | incWork (owner : L) (register : Reg5) (next : L)
      (phase : FoundationStoneTest16BK.IncLabel)
  | divWork (owner : L) (register : Reg5) (positive zero : L)
      (phase : FoundationStoneTest16AV.Label)
  | divRoute (owner : L) (register : Reg5) (positive zero : L)
      (remainder : Nat)
  | posWork (owner : L) (register : Reg5) (positive : L) (phase : TLabel)
  | restoreWork (owner : L) (register : Reg5) (zero : L) (remainder : Nat)
      (phase : FoundationStoneTest16BL.RestoreLabel)
  | jump (target : L)
deriving Repr

def startLabel {L : Type} (P : L → FoundationStoneTest16AY.Instr 5 L) (l : L) :
    GlobalLabel L :=
  match P l with
  | .halt => .halted l
  | .inc i next => .incWork l i next (.mul .loop)
  | .dec i positive zero => .divWork l i positive zero (.scan 0)

def mapBK {L : Type} (owner : L) (i : Reg5) (next : L) :
    Instr FoundationStoneTest16BK.IncLabel → Instr (GlobalLabel L)
  | .inc body l => .inc body (.incWork owner i next l)
  | .dec body p z => .dec body (.incWork owner i next p) (.incWork owner i next z)
  | .halt => .halt

def mapAV {L : Type} (owner : L) (i : Reg5) (positive zero : L) :
    FoundationStoneTest16AV.Instr → Instr (GlobalLabel L)
  | .inc body l => .inc body (.divWork owner i positive zero l)
  | .dec body p z => .dec body (.divWork owner i positive zero p)
      (.divWork owner i positive zero z)
  | .halt => .halt

def mapTransfer {L : Type} (owner : L) (i : Reg5) (positive : L) :
    Instr TLabel → Instr (GlobalLabel L)
  | .inc body l => .inc body (.posWork owner i positive l)
  | .dec body p z => .dec body (.posWork owner i positive p) (.posWork owner i positive z)
  | .halt => .halt

def mapRestore {L : Type} (owner : L) (i : Reg5) (zero : L) (r : Nat) :
    Instr FoundationStoneTest16BL.RestoreLabel → Instr (GlobalLabel L)
  | .inc body l => .inc body (.restoreWork owner i zero r l)
  | .dec body p z => .dec body (.restoreWork owner i zero r p)
      (.restoreWork owner i zero r z)
  | .halt => .halt

/-- One global literal two-counter program. -/
def globalProgram {L : Type} (P : L → FoundationStoneTest16AY.Instr 5 L) :
    GlobalLabel L → Instr (GlobalLabel L)
  | .halted _ => .halt
  | .incWork owner i next .done => .inc false (.jump next)
  | .incWork owner i next phase =>
      mapBK owner i next (FoundationStoneTest16BK.incBlock
        (FoundationStoneTest16BJ.prime i) phase)
  | .divWork owner i positive zero (.exit r) =>
      .inc false (.divRoute owner i positive zero r)
  | .divWork owner i positive zero phase =>
      mapAV owner i positive zero
        (FoundationStoneTest16AV.divProgram (FoundationStoneTest16BJ.prime i) phase)
  | .divRoute owner i positive zero r =>
      let target := if r = 0 then .posWork owner i positive .loop
        else .restoreWork owner i zero r (.transfer .loop)
      .dec false target target
  | .posWork owner i positive .exit => .inc false (.jump positive)
  | .posWork owner i positive phase =>
      mapTransfer owner i positive (transferProgram phase)
  | .restoreWork owner i zero r .done => .inc false (.jump zero)
  | .restoreWork owner i zero r phase =>
      mapRestore owner i zero r
        (FoundationStoneTest16BL.restoreProgram (FoundationStoneTest16BJ.prime i) r phase)
  | .jump target => .dec false (startLabel P target) (startLabel P target)

def wrapBK {L : Type} (owner : L) (i : Reg5) (next : L)
    (s : State FoundationStoneTest16BK.IncLabel) : State (GlobalLabel L) :=
  ⟨.incWork owner i next s.pc, s.a, s.b⟩

def wrapTransfer {L : Type} (owner : L) (i : Reg5) (positive : L)
    (s : State TLabel) : State (GlobalLabel L) :=
  ⟨.posWork owner i positive s.pc, s.a, s.b⟩

def wrapRestore {L : Type} (owner : L) (i : Reg5) (zero : L) (r : Nat)
    (s : State FoundationStoneTest16BL.RestoreLabel) : State (GlobalLabel L) :=
  ⟨.restoreWork owner i zero r s.pc, s.a, s.b⟩

def wrapAV {L : Type} (owner : L) (i : Reg5) (positive zero : L)
    (s : FoundationStoneTest16AV.State) : State (GlobalLabel L) :=
  ⟨.divWork owner i positive zero s.pc, s.a, s.b⟩

/-! ## Local embeddings -/

theorem run_map_of_step {L K : Type} (P : L → Instr L) (Q : K → Instr K)
    (f : State L → State K)
    (hs : ∀ s t, step P s = some t → step Q (f s) = some (f t)) :
    ∀ n s t, run P n s = some t → run Q n (f s) = some (f t) := by
  intro n
  induction n with
  | zero =>
      intro s t h
      simp only [run, Option.some.injEq] at h ⊢
      subst t
      rfl
  | succ n ih =>
      intro s t h
      unfold run at h ⊢
      cases h1 : step P s with
      | none => rw [h1] at h; contradiction
      | some s' =>
          rw [h1] at h
          rw [hs s s' h1]
          exact ih s' t h

theorem bk_step_embeds {L : Type} (P : L → FoundationStoneTest16AY.Instr 5 L)
    (owner : L) (i : Reg5) (next : L)
    (s t : State FoundationStoneTest16BK.IncLabel)
    (h : step (FoundationStoneTest16BK.incBlock (FoundationStoneTest16BJ.prime i)) s = some t) :
    step (globalProgram P) (wrapBK owner i next s) = some (wrapBK owner i next t) := by
  rcases s with ⟨pc,a,b⟩
  rcases t with ⟨pc',a',b'⟩
  have hdone : pc ≠ FoundationStoneTest16BK.IncLabel.done := by
    intro he; subst pc
    simp [FoundationStoneTest16BK.incBlock, step] at h
  unfold step at h ⊢
  cases hi : FoundationStoneTest16BK.incBlock (FoundationStoneTest16BJ.prime i) pc with
  | halt => simp [hi] at h
  | inc body phase =>
      cases body <;> simp_all [globalProgram, wrapBK, mapBK, hdone,
        FoundationStoneTest16AW.get, FoundationStoneTest16AW.set]
  | dec body positive zero =>
      cases body with
      | false =>
          by_cases hz : a = 0 <;> simp_all [globalProgram, wrapBK, mapBK, hdone,
            FoundationStoneTest16AW.get, FoundationStoneTest16AW.set]
      | true =>
          by_cases hz : b = 0 <;> simp_all [globalProgram, wrapBK, mapBK, hdone,
            FoundationStoneTest16AW.get, FoundationStoneTest16AW.set]

theorem transfer_step_embeds {L : Type} (P : L → FoundationStoneTest16AY.Instr 5 L)
    (owner : L) (i : Reg5) (positive : L) (s t : State TLabel)
    (h : step transferProgram s = some t) :
    step (globalProgram P) (wrapTransfer owner i positive s) =
      some (wrapTransfer owner i positive t) := by
  rcases s with ⟨pc,a,b⟩
  rcases t with ⟨pc',a',b'⟩
  unfold step at h ⊢
  cases pc with
  | exit => simp [transferProgram] at h
  | loop =>
      simp only [transferProgram, globalProgram, mapTransfer, wrapTransfer] at h ⊢
      by_cases hz : b = 0 <;> simp_all [FoundationStoneTest16AW.get,
        FoundationStoneTest16AW.set]
  | credit => simp_all [transferProgram, globalProgram, mapTransfer, wrapTransfer,
      FoundationStoneTest16AW.get, FoundationStoneTest16AW.set]

theorem restore_step_embeds {L : Type} (P : L → FoundationStoneTest16AY.Instr 5 L)
    (owner : L) (i : Reg5) (zero : L) (r : Nat)
    (s t : State FoundationStoneTest16BL.RestoreLabel)
    (h : step (FoundationStoneTest16BL.restoreProgram
      (FoundationStoneTest16BJ.prime i) r) s = some t) :
    step (globalProgram P) (wrapRestore owner i zero r s) =
      some (wrapRestore owner i zero r t) := by
  rcases s with ⟨pc,a,b⟩
  rcases t with ⟨pc',a',b'⟩
  have hdone : pc ≠ FoundationStoneTest16BL.RestoreLabel.done := by
    intro he; subst pc
    simp [FoundationStoneTest16BL.restoreProgram, step] at h
  unfold step at h ⊢
  cases hi : FoundationStoneTest16BL.restoreProgram
      (FoundationStoneTest16BJ.prime i) r pc with
  | halt => simp [hi] at h
  | inc body phase =>
      cases body <;> simp_all [globalProgram, wrapRestore, mapRestore, hdone,
        FoundationStoneTest16AW.get, FoundationStoneTest16AW.set]
  | dec body positive negative =>
      cases body with
      | false =>
          by_cases hz : a = 0 <;> simp_all [globalProgram, wrapRestore, mapRestore, hdone,
            FoundationStoneTest16AW.get, FoundationStoneTest16AW.set]
      | true =>
          by_cases hz : b = 0 <;> simp_all [globalProgram, wrapRestore, mapRestore, hdone,
            FoundationStoneTest16AW.get, FoundationStoneTest16AW.set]

theorem av_step_embeds {L : Type} (P : L → FoundationStoneTest16AY.Instr 5 L)
    (owner : L) (i : Reg5) (positive zero : L)
    (s t : FoundationStoneTest16AV.State)
    (h : FoundationStoneTest16AV.step
      (FoundationStoneTest16AV.divProgram (FoundationStoneTest16BJ.prime i)) s = some t) :
    step (globalProgram P) (wrapAV owner i positive zero s) =
      some (wrapAV owner i positive zero t) := by
  rcases s with ⟨pc,a,b⟩
  rcases t with ⟨pc',a',b'⟩
  unfold FoundationStoneTest16AV.step at h
  unfold step
  cases pc with
  | exit r => simp [FoundationStoneTest16AV.divProgram] at h
  | bad => simp [FoundationStoneTest16AV.divProgram] at h
  | credit => simp_all [FoundationStoneTest16AV.divProgram, globalProgram, mapAV,
      wrapAV, FoundationStoneTest16AV.get, FoundationStoneTest16AV.set,
      FoundationStoneTest16AW.get, FoundationStoneTest16AW.set]
  | scan n =>
      by_cases hlt : n + 1 < FoundationStoneTest16BJ.prime i
      · by_cases hz : a = 0 <;> simp_all [FoundationStoneTest16AV.divProgram,
          globalProgram, mapAV, wrapAV, FoundationStoneTest16AV.get,
          FoundationStoneTest16AV.set, FoundationStoneTest16AW.get,
          FoundationStoneTest16AW.set]
      · by_cases heq : n + 1 = FoundationStoneTest16BJ.prime i
        · by_cases hz : a = 0 <;> simp_all [FoundationStoneTest16AV.divProgram,
            globalProgram, mapAV, wrapAV, FoundationStoneTest16AV.get,
            FoundationStoneTest16AV.set, FoundationStoneTest16AW.get,
            FoundationStoneTest16AW.set]
        · simp_all [FoundationStoneTest16AV.divProgram]

theorem bk_run_embeds {L : Type} (P : L → FoundationStoneTest16AY.Instr 5 L)
    (owner : L) (i : Reg5) (next : L) : ∀ n s t,
    run (FoundationStoneTest16BK.incBlock (FoundationStoneTest16BJ.prime i)) n s = some t →
    run (globalProgram P) n (wrapBK owner i next s) = some (wrapBK owner i next t) :=
  run_map_of_step _ _ (wrapBK owner i next)
    (bk_step_embeds P owner i next)

theorem transfer_run_embeds {L : Type} (P : L → FoundationStoneTest16AY.Instr 5 L)
    (owner : L) (i : Reg5) (positive : L) : ∀ n s t,
    run transferProgram n s = some t →
    run (globalProgram P) n (wrapTransfer owner i positive s) =
      some (wrapTransfer owner i positive t) :=
  run_map_of_step _ _ (wrapTransfer owner i positive)
    (transfer_step_embeds P owner i positive)

theorem restore_run_embeds {L : Type} (P : L → FoundationStoneTest16AY.Instr 5 L)
    (owner : L) (i : Reg5) (zero : L) (r : Nat) : ∀ n s t,
    run (FoundationStoneTest16BL.restoreProgram (FoundationStoneTest16BJ.prime i) r) n s = some t →
    run (globalProgram P) n (wrapRestore owner i zero r s) =
      some (wrapRestore owner i zero r t) :=
  run_map_of_step _ _ (wrapRestore owner i zero r)
    (restore_step_embeds P owner i zero r)

theorem av_run_embeds {L : Type} (P : L → FoundationStoneTest16AY.Instr 5 L)
    (owner : L) (i : Reg5) (positive zero : L) : ∀ n s t,
    FoundationStoneTest16AV.run
        (FoundationStoneTest16AV.divProgram (FoundationStoneTest16BJ.prime i)) n s = some t →
    run (globalProgram P) n (wrapAV owner i positive zero s) =
      some (wrapAV owner i positive zero t) := by
  intro n
  induction n with
  | zero =>
      intro s t h
      simp only [FoundationStoneTest16AV.run, run, Option.some.injEq] at h ⊢
      subst t; rfl
  | succ n ih =>
      intro s t h
      unfold FoundationStoneTest16AV.run at h
      unfold run
      cases h1 : FoundationStoneTest16AV.step
          (FoundationStoneTest16AV.divProgram (FoundationStoneTest16BJ.prime i)) s with
      | none => rw [h1] at h; contradiction
      | some s' =>
          rw [h1] at h
          rw [av_step_embeds P owner i positive zero s s' h1]
          exact ih s' t h

/-! ## Typed bridges and exact compiled instructions -/

theorem jump_exact {L : Type} (P : L → FoundationStoneTest16AY.Instr 5 L)
    (target : L) (a : Nat) :
    run (globalProgram P) 1 ⟨GlobalLabel.jump target, a + 1, 0⟩ =
      some ⟨startLabel P target, a, 0⟩ := by
  simp [run, step, globalProgram, FoundationStoneTest16AW.get,
    FoundationStoneTest16AW.set]

theorem inc_compiled_exact {L : Type} (P : L → FoundationStoneTest16AY.Instr 5 L)
    (owner next : L) (i : Reg5) (a : Nat) :
    ∃ steps, 0 < steps ∧ run (globalProgram P) steps
        ⟨GlobalLabel.incWork owner i next (.mul .loop), a, 0⟩ =
      some ⟨startLabel P next, FoundationStoneTest16BJ.prime i * a, 0⟩ := by
  let n := (3 * FoundationStoneTest16BJ.prime i + 1) * a + 6
  have hb := bk_run_embeds P owner i next n
    (⟨FoundationStoneTest16BK.IncLabel.mul .loop, a, 0⟩ :
      State FoundationStoneTest16BK.IncLabel)
    (⟨FoundationStoneTest16BK.IncLabel.done,
      FoundationStoneTest16BJ.prime i * a, 0⟩ :
      State FoundationStoneTest16BK.IncLabel)
    (by simpa [n] using (FoundationStoneTest16BK.inc_block_exact
      (FoundationStoneTest16BJ.prime i) a
      (FoundationStoneTest16BK.selected_prime_positive i)))
  simp only [wrapBK] at hb
  refine ⟨n + 2, by omega, ?_⟩
  rw [run_add, hb]
  simp only
  simp [run, step, globalProgram, FoundationStoneTest16AW.get,
    FoundationStoneTest16AW.set]

theorem div_route_zero {L : Type} (P : L → FoundationStoneTest16AY.Instr 5 L)
    (owner : L) (i : Reg5) (positive zero : L) (q : Nat) :
    run (globalProgram P) 2
        ⟨GlobalLabel.divWork owner i positive zero (.exit 0), 0, q⟩ =
      some ⟨GlobalLabel.posWork owner i positive .loop, 0, q⟩ := by
  simp [run, step, globalProgram, FoundationStoneTest16AW.get,
    FoundationStoneTest16AW.set]

theorem div_route_nonzero {L : Type} (P : L → FoundationStoneTest16AY.Instr 5 L)
    (owner : L) (i : Reg5) (positive zero : L) (r q : Nat) (hr : r ≠ 0) :
    run (globalProgram P) 2
        ⟨GlobalLabel.divWork owner i positive zero (.exit r), 0, q⟩ =
      some ⟨GlobalLabel.restoreWork owner i zero r (.transfer .loop), 0, q⟩ := by
  simp [run, step, globalProgram, hr, FoundationStoneTest16AW.get,
    FoundationStoneTest16AW.set]

theorem dec_positive_compiled_exact {L : Type}
    (P : L → FoundationStoneTest16AY.Instr 5 L) (owner : L) (i : Reg5)
    (positive zero : L) (a : Nat) (hd : FoundationStoneTest16BJ.prime i ∣ a) :
    ∃ steps, 0 < steps ∧ run (globalProgram P) steps
        ⟨GlobalLabel.divWork owner i positive zero (.scan 0), a, 0⟩ =
      some ⟨startLabel P positive, a / FoundationStoneTest16BJ.prime i, 0⟩ := by
  let p := FoundationStoneTest16BJ.prime i
  let nd := (p + 1) * (a / p) + (a % p + 1)
  let nt := 2 * (a / p) + 1
  have hp := FoundationStoneTest16BK.selected_prime_positive i
  have hm : a % p = 0 := Nat.mod_eq_zero_of_dvd hd
  have hdv := av_run_embeds P owner i positive zero nd
    (⟨FoundationStoneTest16AV.Label.scan 0, a, 0⟩ : FoundationStoneTest16AV.State)
    (⟨FoundationStoneTest16AV.Label.exit 0, 0, a / p⟩ : FoundationStoneTest16AV.State)
    (by simpa [nd, p, hm] using FoundationStoneTest16BL.division_probe_exact p a hp)
  have ht := transfer_run_embeds P owner i positive nt
    (⟨TLabel.loop, 0, a / p⟩ : State TLabel)
    (⟨TLabel.exit, a / p, 0⟩ : State TLabel)
    (by simpa [nt] using transfer_exact 0 (a / p))
  simp only [wrapAV] at hdv
  simp only [wrapTransfer] at ht
  refine ⟨nd + 2 + nt + 2, by omega, ?_⟩
  rw [run_add, run_add, run_add, hdv]
  simp only
  rw [div_route_zero]
  simp only
  rw [ht]
  simp only
  simp [run, step, globalProgram, p, FoundationStoneTest16AW.get,
    FoundationStoneTest16AW.set]

theorem dec_zero_compiled_exact {L : Type}
    (P : L → FoundationStoneTest16AY.Instr 5 L) (owner : L) (i : Reg5)
    (positive zero : L) (a : Nat) (hnd : ¬ FoundationStoneTest16BJ.prime i ∣ a) :
    ∃ steps, 0 < steps ∧ run (globalProgram P) steps
        ⟨GlobalLabel.divWork owner i positive zero (.scan 0), a, 0⟩ =
      some ⟨startLabel P zero, a, 0⟩ := by
  let p := FoundationStoneTest16BJ.prime i
  let r := a % p
  let nd := (p + 1) * (a / p) + (r + 1)
  have hp := FoundationStoneTest16BK.selected_prime_positive i
  have hr : r ≠ 0 := by
    intro h
    exact hnd ((Nat.dvd_iff_mod_eq_zero).2 h)
  have hdv := av_run_embeds P owner i positive zero nd
    (⟨FoundationStoneTest16AV.Label.scan 0, a, 0⟩ : FoundationStoneTest16AV.State)
    (⟨FoundationStoneTest16AV.Label.exit r, 0, a / p⟩ : FoundationStoneTest16AV.State)
    (by simpa [nd, r, p] using FoundationStoneTest16BL.division_probe_exact p a hp)
  obtain ⟨nr, hrest0⟩ := FoundationStoneTest16BL.restore_nonzero_remainder
    p (a / p) r hp (Nat.pos_of_ne_zero hr)
  have hrest := restore_run_embeds P owner i zero r nr
    (⟨FoundationStoneTest16BL.RestoreLabel.transfer .loop, 0, a / p⟩ :
      State FoundationStoneTest16BL.RestoreLabel)
    (⟨FoundationStoneTest16BL.RestoreLabel.done, p * (a / p) + r, 0⟩ :
      State FoundationStoneTest16BL.RestoreLabel) hrest0
  have ha : p * (a / p) + r = a := by
    simpa [p, r, Nat.mul_comm] using Nat.div_add_mod a p
  simp only [wrapAV] at hdv
  simp only [wrapRestore] at hrest
  refine ⟨nd + 2 + nr + 2, by omega, ?_⟩
  rw [run_add, run_add, run_add, hdv]
  simp only
  rw [div_route_nonzero P owner i positive zero r (a / p) hr]
  simp only
  rw [hrest]
  simp only
  rw [ha]
  simp [run, step, globalProgram, FoundationStoneTest16AW.get,
    FoundationStoneTest16AW.set]

/-! ## The global simulation -/

def encode {L : Type} (P : L → FoundationStoneTest16AY.Instr 5 L)
    (s : FoundationStoneTest16AY.State 5 L) : State (GlobalLabel L) :=
  ⟨startLabel P s.pc,
    FoundationStoneTest16AM.pack (FoundationStoneTest16BJ.fromVec s.counters), 0⟩

def Encodes {L : Type} (P : L → FoundationStoneTest16AY.Instr 5 L)
    (s : FoundationStoneTest16AY.State 5 L) (t : State (GlobalLabel L)) : Prop :=
  encode P s = t

theorem global_respects {L : Type} (P : L → FoundationStoneTest16AY.Instr 5 L) :
    StateTransition.Respects (FoundationStoneTest16AY.step P)
      (step (globalProgram P)) (Encodes P) := by
  intro s t hst
  subst t
  cases hi : P s.pc with
  | halt =>
      have hs : FoundationStoneTest16AY.step P s = none := by
        simp [FoundationStoneTest16AY.step, hi]
      rw [hs]
      simp [encode, startLabel, hi, globalProgram, step]
  | inc i next =>
      let s' := FoundationStoneTest16AY.setCounter s next i (s.counters i + 1)
      have hs : FoundationStoneTest16AY.step P s = some s' := by
        simp [FoundationStoneTest16AY.step, hi, s']
      rw [hs]
      refine ⟨encode P s', rfl, ?_⟩
      obtain ⟨n, hnpos, hn⟩ := inc_compiled_exact P s.pc next i
        (FoundationStoneTest16AM.pack (FoundationStoneTest16BJ.fromVec s.counters))
      apply FoundationStoneTest16BI.positive_run_gives_reaches
        (globalProgram P) n hnpos
      have hrun : run (globalProgram P) n (encode P s) =
          some (encode P s') := by
        simpa only [encode, startLabel, hi, s', FoundationStoneTest16AY.setCounter,
          FoundationStoneTest16BJ.pack_update_inc] using hn
      exact hrun
  | dec i positive zero =>
      by_cases hz : s.counters i = 0
      · let s' : FoundationStoneTest16AY.State 5 L := { s with pc := zero }
        have hs : FoundationStoneTest16AY.step P s = some s' := by
          simp [FoundationStoneTest16AY.step, hi, hz, s']
        rw [hs]
        refine ⟨encode P s', rfl, ?_⟩
        have hnd : ¬ FoundationStoneTest16BJ.prime i ∣
            FoundationStoneTest16AM.pack (FoundationStoneTest16BJ.fromVec s.counters) := by
          rw [FoundationStoneTest16BJ.prime_dvd_pack_iff]
          omega
        obtain ⟨n, hnpos, hn⟩ := dec_zero_compiled_exact P s.pc i positive zero _ hnd
        apply FoundationStoneTest16BI.positive_run_gives_reaches
          (globalProgram P) n hnpos
        simpa only [encode, startLabel, hi, s'] using hn
      · have hp : 0 < s.counters i := Nat.pos_of_ne_zero hz
        let s' := FoundationStoneTest16AY.setCounter s positive i (s.counters i - 1)
        have hs : FoundationStoneTest16AY.step P s = some s' := by
          simp [FoundationStoneTest16AY.step, hi, hz, s']
        rw [hs]
        refine ⟨encode P s', rfl, ?_⟩
        have hd : FoundationStoneTest16BJ.prime i ∣
            FoundationStoneTest16AM.pack (FoundationStoneTest16BJ.fromVec s.counters) :=
          (FoundationStoneTest16BJ.prime_dvd_pack_iff s.counters i).2 hp
        obtain ⟨n, hnpos, hn⟩ := dec_positive_compiled_exact P s.pc i positive zero _ hd
        apply FoundationStoneTest16BI.positive_run_gives_reaches
          (globalProgram P) n hnpos
        have hrun : run (globalProgram P) n (encode P s) =
            some (encode P s') := by
          simpa only [encode, startLabel, hi, s', FoundationStoneTest16AY.setCounter,
            FoundationStoneTest16BJ.pack_update_dec _ i hp] using hn
        exact hrun

def FiveTerminates {L : Type} (P : L → FoundationStoneTest16AY.Instr 5 L)
    (s : FoundationStoneTest16AY.State 5 L) : Prop :=
  (StateTransition.eval (FoundationStoneTest16AY.step P) s).Dom

def MM2Terminates {L : Type} (P : L → FoundationStoneTest16AY.Instr 5 L)
    (s : State (GlobalLabel L)) : Prop :=
  (StateTransition.eval (step (globalProgram P)) s).Dom

theorem global_halting_iff {L : Type} (P : L → FoundationStoneTest16AY.Instr 5 L)
    (s : FoundationStoneTest16AY.State 5 L) :
    FiveTerminates P s ↔ MM2Terminates P (encode P s) := by
  unfold FiveTerminates MM2Terminates
  exact (StateTransition.tr_eval_dom (global_respects P) rfl).symm

/-! Red control: a target that halts at every internal entry cannot respect a
source increment, because `Respects` requires a positive target run. -/
def brokenProgram {L : Type} (_ : GlobalLabel L) : Instr (GlobalLabel L) := .halt

theorem broken_cannot_implement_increment {L : Type} (P : L → FoundationStoneTest16AY.Instr 5 L)
    (l next : L) (i : Reg5) (hP : P l = .inc i next)
    (c : Reg5 → Nat) :
    ¬ Relation.TransGen
      (fun u v => step (@brokenProgram L) u = some v)
      ⟨startLabel P l, FoundationStoneTest16AM.pack (FoundationStoneTest16BJ.fromVec c), 0⟩
      ⟨startLabel P next,
        FoundationStoneTest16AM.pack
          (FoundationStoneTest16BJ.fromVec (Function.update c i (c i + 1))), 0⟩ := by
  intro h
  obtain ⟨mid, hfirst, _⟩ := Relation.TransGen.head'_iff.mp h
  simp [step, brokenProgram] at hfirst

theorem turing_chamber_16BM_certificate :
    (∀ {L : Type} (P : L → FoundationStoneTest16AY.Instr 5 L),
      StateTransition.Respects (FoundationStoneTest16AY.step P)
        (step (globalProgram P)) (Encodes P)) ∧
    (∀ {L : Type} (P : L → FoundationStoneTest16AY.Instr 5 L)
      (s : FoundationStoneTest16AY.State 5 L),
      FiveTerminates P s ↔ MM2Terminates P (encode P s)) :=
  ⟨global_respects, global_halting_iff⟩

#print axioms inc_compiled_exact
#print axioms dec_positive_compiled_exact
#print axioms dec_zero_compiled_exact
#print axioms global_respects
#print axioms global_halting_iff
#print axioms turing_chamber_16BM_certificate

end FoundationStoneTest16BM
