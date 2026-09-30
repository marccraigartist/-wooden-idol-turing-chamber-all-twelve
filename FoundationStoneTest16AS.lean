import Mathlib

/-!
# THE TURING CHAMBER — TEST 16AS: THE PARAMETRIC PRIME GATE

Lean 4.35.0-rc2 / pinned Mathlib.

The literal MM2 gates in 16AK (`k=5`) and 16AO (`k=2`) share one algorithm:
repeatedly remove a complete group of `k` tokens from A and credit one token
to B; when fewer than `k` remain, expose that remainder in finite control.

This file proves the algorithm once for every `k>0`.  Its transition is the
macro boundary that the later flattening proof must refine to primitive MM2
instructions.  Division and remainder occur only in the theorem statement,
not in the transition function.
-/

namespace FoundationStoneTest16AS

inductive Phase
  | work
  | exit (remainder : Nat)
deriving DecidableEq, Repr

structure State where
  phase : Phase
  a : Nat
  b : Nat
deriving DecidableEq, Repr

/-- One macro-step removes exactly one complete group, or exits carrying the
strictly smaller remainder. -/
def step (k : Nat) : State → Option State
  | ⟨.work, a, b⟩ =>
      if k ≤ a then some ⟨.work, a - k, b + 1⟩
      else some ⟨.exit a, a, b⟩
  | ⟨.exit _, _, _⟩ => none

def run (k : Nat) : Nat → State → Option State
  | 0, s => some s
  | n + 1, s =>
      match step k s with
      | none => none
      | some s' => run k n s'

theorem run_add (k m : Nat) : ∀ n s,
    run k (m + n) s =
      match run k m s with
      | none => none
      | some s' => run k n s' := by
  intro n
  induction m with
  | zero => intro s; simp [run]
  | succ m ih =>
      intro s
      simp only [Nat.succ_add, run]
      cases step k s with
      | none => rfl
      | some s' => exact ih s'

theorem one_group (k a b : Nat) (h : k ≤ a) :
    run k 1 ⟨.work, a, b⟩ = some ⟨.work, a - k, b + 1⟩ := by
  simp [run, step, h]

theorem complete_groups (k q r b : Nat) (hk : 0 < k) :
    run k q ⟨.work, k * q + r, b⟩ = some ⟨.work, r, b + q⟩ := by
  induction q generalizing r b with
  | zero => simp [run]
  | succ q ih =>
      have ha : k * (q + 1) + r = k * q + (k + r) := by
        simp [Nat.mul_succ, Nat.add_assoc, Nat.add_comm k r]
      rw [ha, show q + 1 = q + 1 from rfl, run_add, ih (k + r) b]
      simp only
      rw [one_group]
      · simp only [Nat.add_sub_cancel_left]
        congr 2
      · omega

theorem remainder_exit (k r b : Nat) (hr : r < k) :
    run k 1 ⟨.work, r, b⟩ = some ⟨.exit r, r, b⟩ := by
  simp [run, step, Nat.not_le.mpr hr]

/-- Exact quotient/remainder contract for every positive grouping size. -/
theorem divmod_exact (k n b : Nat) (hk : 0 < k) :
    run k (n / k + 1) ⟨.work, n, b⟩ =
      some ⟨.exit (n % k), n % k, b + n / k⟩ := by
  have hn : k * (n / k) + n % k = n := by
    simpa [Nat.mul_comm] using Nat.div_add_mod n k
  rw [show n / k + 1 = n / k + 1 from rfl, run_add]
  have hg := complete_groups k (n / k) (n % k) b hk
  rw [hn] at hg
  rw [hg]
  simp only
  exact remainder_exit k (n % k) (b + n / k) (Nat.mod_lt _ hk)

/-- Divisibility is exactly exit through remainder zero. -/
theorem zero_exit_iff_dvd (k n : Nat) (hk : 0 < k) :
    n % k = 0 ↔ k ∣ n := by
  exact (@Nat.dvd_iff_mod_eq_zero k n).symm

/-! Red control: if the exit forgets its remainder, zero and nonzero branches
collapse even though the quotient calculation remains correct. -/

def forgetRemainder : Phase → Bool
  | .work => false
  | .exit _ => true

theorem forgetting_remainder_collapses (k : Nat) :
    forgetRemainder (.exit 0) = forgetRemainder (.exit k) := rfl

theorem turing_chamber_16AS_certificate (k n b : Nat) (hk : 0 < k) :
    run k (n / k + 1) ⟨.work, n, b⟩ =
      some ⟨.exit (n % k), n % k, b + n / k⟩ ∧
    (n % k = 0 ↔ k ∣ n) ∧
    forgetRemainder (.exit 0) = forgetRemainder (.exit k) :=
  ⟨divmod_exact k n b hk, zero_exit_iff_dvd k n hk,
   forgetting_remainder_collapses k⟩

#print axioms divmod_exact
#print axioms zero_exit_iff_dvd
#print axioms turing_chamber_16AS_certificate

end FoundationStoneTest16AS
