import FoundationStoneTest16BJ

/-!
# THE TURING CHAMBER — TEST 16BK: PHYSICAL PRIME INCREMENT

Lean 4.35.0-rc2 / pinned Mathlib.

16BJ's packed increment is multiplication by the selected prime.  Here that
macro operation is lowered to literal two-counter instructions.  The block
first consumes A while adding `p` tokens to B for each token removed, then
transfers B back to A.  Its two internal joins use increment/decrement bridges
that preserve both counters and have typed destinations.

Lean proves the exact run, including its exact step count, for every `p > 0`:

  (A=n, B=0)  -->  (A=p*n, B=0).

It is then instantiated for all five packed registers, so every primitive
five-counter increment from 16BJ now has a genuine primitive MM2 block.
Division and the zero/nonzero branch are deliberately left to 16BL.
-/

namespace FoundationStoneTest16BK

open FoundationStoneTest16AW

inductive IncLabel
  | mul (l : MLabel)
  | mulBridge
  | transfer (l : TLabel)
  | transferBridge
  | done
deriving DecidableEq, Repr

def mapMulInstr : Instr MLabel → Instr IncLabel
  | .inc body next => .inc body (.mul next)
  | .dec body positive zero => .dec body (.mul positive) (.mul zero)
  | .halt => .halt

def mapTransferInstr : Instr TLabel → Instr IncLabel
  | .inc body next => .inc body (.transfer next)
  | .dec body positive zero => .dec body (.transfer positive) (.transfer zero)
  | .halt => .halt

/-- A literal primitive two-counter program.  Only `inc`, `dec/zero`, and
explicit `halt` occur. -/
def incBlock (p : Nat) : IncLabel → Instr IncLabel
  | .mul .exit => .inc false .mulBridge
  | .mul l => mapMulInstr (mulProgram p l)
  | .mulBridge => .dec false (.transfer .loop) (.transfer .loop)
  | .transfer .exit => .inc false .transferBridge
  | .transfer l => mapTransferInstr (transferProgram l)
  | .transferBridge => .dec false .done .done
  | .done => .halt

def mapMulState (s : State MLabel) : State IncLabel := ⟨.mul s.pc, s.a, s.b⟩
def mapTransferState (s : State TLabel) : State IncLabel := ⟨.transfer s.pc, s.a, s.b⟩

theorem mul_step_embeds (p : Nat) (s t : State MLabel)
    (h : step (mulProgram p) s = some t) :
    step (incBlock p) (mapMulState s) = some (mapMulState t) := by
  rcases s with ⟨pc, a, b⟩
  rcases t with ⟨pc', a', b'⟩
  unfold step at h ⊢
  cases pc with
  | exit => simp [mulProgram] at h
  | loop =>
      simp only [mulProgram, incBlock, mapMulInstr, mapMulState] at h ⊢
      by_cases hz : a = 0 <;> simp_all [FoundationStoneTest16AW.get,
        FoundationStoneTest16AW.set]
  | add d =>
      cases d with
      | zero => simp [mulProgram] at h
      | succ d =>
          by_cases hd : d = 0 <;>
            simp_all [mulProgram, incBlock, mapMulInstr, mapMulState,
              FoundationStoneTest16AW.get, FoundationStoneTest16AW.set]

theorem transfer_step_embeds (s t : State TLabel)
    (h : step transferProgram s = some t) :
    step (incBlock p) (mapTransferState s) = some (mapTransferState t) := by
  rcases s with ⟨pc, a, b⟩
  rcases t with ⟨pc', a', b'⟩
  unfold step at h ⊢
  cases pc with
  | exit => simp [transferProgram] at h
  | loop =>
      simp only [transferProgram, incBlock, mapTransferInstr, mapTransferState] at h ⊢
      by_cases hz : b = 0 <;> simp_all [FoundationStoneTest16AW.get,
        FoundationStoneTest16AW.set]
  | credit => simp_all [transferProgram, incBlock, mapTransferInstr,
      mapTransferState, FoundationStoneTest16AW.get, FoundationStoneTest16AW.set]

theorem mul_run_embeds (p : Nat) : ∀ n s t,
    run (mulProgram p) n s = some t →
    run (incBlock p) n (mapMulState s) = some (mapMulState t) := by
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
      cases hs : step (mulProgram p) s with
      | none => rw [hs] at h; contradiction
      | some s' =>
          rw [hs] at h
          rw [mul_step_embeds p s s' hs]
          exact ih s' t h

theorem transfer_run_embeds (p : Nat) : ∀ n s t,
    run transferProgram n s = some t →
    run (incBlock p) n (mapTransferState s) = some (mapTransferState t) := by
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
      cases hs : step transferProgram s with
      | none => rw [hs] at h; contradiction
      | some s' =>
          rw [hs] at h
          rw [transfer_step_embeds s s' hs]
          exact ih s' t h

theorem mul_bridge_exact (p q : Nat) :
    run (incBlock p) 2 ⟨.mul .exit, 0, q⟩ =
      some ⟨.transfer .loop, 0, q⟩ := by
  simp [run, step, incBlock, FoundationStoneTest16AW.get,
    FoundationStoneTest16AW.set]

theorem transfer_bridge_exact (p q : Nat) :
    run (incBlock p) 2 ⟨.transfer .exit, q, 0⟩ =
      some ⟨.done, q, 0⟩ := by
  simp [run, step, incBlock, FoundationStoneTest16AW.get,
    FoundationStoneTest16AW.set]

/-- Exact primitive-MM2 implementation of multiplication by `p`. -/
theorem inc_block_exact (p n : Nat) (hp : 0 < p) :
    run (incBlock p) ((3 * p + 1) * n + 6) ⟨.mul .loop, n, 0⟩ =
      some ⟨.done, p * n, 0⟩ := by
  have hm := mul_run_embeds p ((p + 1) * n + 1)
    (⟨MLabel.loop, n, 0⟩ : State MLabel)
    (⟨MLabel.exit, 0, p * n⟩ : State MLabel)
    (multiply_exact p n hp)
  have ht := transfer_run_embeds p (2 * (p * n) + 1)
    (⟨TLabel.loop, 0, p * n⟩ : State TLabel)
    (⟨TLabel.exit, p * n, 0⟩ : State TLabel)
    (by simpa using transfer_exact 0 (p * n))
  simp only [mapMulState] at hm
  simp only [mapTransferState] at ht
  rw [show (3 * p + 1) * n + 6 =
      ((p + 1) * n + 1) + 2 + (2 * (p * n) + 1) + 2 by ring]
  rw [run_add, run_add, run_add, hm]
  simp only
  rw [mul_bridge_exact]
  simp only
  rw [ht]
  simp only
  rw [transfer_bridge_exact]

theorem selected_prime_positive (i : FoundationStoneTest16BJ.Reg5) :
    0 < FoundationStoneTest16BJ.prime i := by
  fin_cases i <;> decide

/-- Every 16BJ packed increment now has a literal primitive two-counter run. -/
theorem packed_increment_is_physical
    (c : FoundationStoneTest16BJ.Reg5 → Nat)
    (i : FoundationStoneTest16BJ.Reg5) :
    let a := FoundationStoneTest16AM.pack (FoundationStoneTest16BJ.fromVec c)
    run (incBlock (FoundationStoneTest16BJ.prime i))
        ((3 * FoundationStoneTest16BJ.prime i + 1) * a + 6)
        ⟨.mul .loop, a, 0⟩ =
      some ⟨.done,
        FoundationStoneTest16AM.pack
          (FoundationStoneTest16BJ.fromVec (Function.update c i (c i + 1))), 0⟩ := by
  dsimp only
  rw [FoundationStoneTest16BJ.pack_update_inc]
  exact inc_block_exact _ _ (selected_prime_positive i)

theorem inc_block_halts_only_at_done_or_invalid (p : Nat) :
    step (incBlock p) ⟨IncLabel.done, 0, 0⟩ = none := rfl

/-! Red control: stopping after multiplication leaves the value in B, not A. -/
theorem multiplication_without_restore_is_wrong (p n : Nat) (hp : 0 < p)
    (hn : 0 < n) :
    (mapMulState ⟨MLabel.exit, 0, p * n⟩).a ≠ p * n := by
  simp [mapMulState]
  exact ⟨hp.ne', hn.ne'⟩

theorem turing_chamber_16BK_certificate :
    (∀ p n, 0 < p →
      run (incBlock p) ((3 * p + 1) * n + 6) ⟨IncLabel.mul .loop, n, 0⟩ =
        some ⟨IncLabel.done, p * n, 0⟩) ∧
    (∀ c i,
      let a := FoundationStoneTest16AM.pack (FoundationStoneTest16BJ.fromVec c)
      run (incBlock (FoundationStoneTest16BJ.prime i))
          ((3 * FoundationStoneTest16BJ.prime i + 1) * a + 6)
          ⟨IncLabel.mul .loop, a, 0⟩ =
        some ⟨IncLabel.done,
          FoundationStoneTest16AM.pack
            (FoundationStoneTest16BJ.fromVec (Function.update c i (c i + 1))), 0⟩) :=
  ⟨inc_block_exact, packed_increment_is_physical⟩

#print axioms inc_block_exact
#print axioms selected_prime_positive
#print axioms packed_increment_is_physical
#print axioms multiplication_without_restore_is_wrong
#print axioms turing_chamber_16BK_certificate

end FoundationStoneTest16BK
