import Mathlib

/-! Structural Chapter 7: two lanes, six occupied positions per lane, indefinitely many
encounters. This source does not yet assert Phase6Godel's all-twelve theorem. -/
namespace Chapter7PipelineCore
set_option autoImplicit false

structure Passenger (Body : Type) where
  id : Nat
  entered : Nat
  body : Body

def evolve {Body : Type} (f : Body → Body) (p : Passenger Body) : Passenger Body :=
  { p with body := f p.body }

@[simp] theorem evolve_id {Body : Type} (f : Body → Body) (p : Passenger Body) :
    (evolve f p).id = p.id := rfl

@[simp] theorem evolve_option_ids {Body : Type} (f : Body → Body)
    (o : Option (Passenger Body)) :
    ((o.map (evolve f)).toList.map Passenger.id) =
      (o.toList.map Passenger.id) := by
  cases o <;> rfl

structure Lane (Body : Type) where
  b3 : Option (Passenger Body) := none
  b4 : Option (Passenger Body) := none
  b5 : Option (Passenger Body) := none
  b6 : Option (Passenger Body) := none
  b7 : Option (Passenger Body) := none
  b8 : Option (Passenger Body) := none
  released : List (Passenger Body) := []

def Lane.tick {Body : Type} (f : Body → Body)
    (new : Passenger Body) (l : Lane Body) : Lane Body :=
  { b3 := some new
    b4 := l.b3.map (evolve f)
    b5 := l.b4.map (evolve f)
    b6 := l.b5.map (evolve f)
    b7 := l.b6.map (evolve f)
    b8 := l.b7.map (evolve f)
    released := (l.b8.map (evolve f)).toList ++ l.released }

def Lane.ids {Body : Type} (l : Lane Body) : List Nat :=
  l.b3.toList.map Passenger.id ++ l.b4.toList.map Passenger.id ++
  l.b5.toList.map Passenger.id ++ l.b6.toList.map Passenger.id ++
  l.b7.toList.map Passenger.id ++ l.b8.toList.map Passenger.id ++
  l.released.map Passenger.id

theorem Lane.ids_tick {Body : Type} (l : Lane Body)
    (f : Body → Body) (new : Passenger Body) :
    (l.tick f new).ids = new.id :: l.ids := by
  simp [Lane.ids, Lane.tick, List.append_assoc]

def Lane.full {Body : Type} (l : Lane Body) : Prop :=
  l.b3.isSome = true ∧ l.b4.isSome = true ∧ l.b5.isSome = true ∧
  l.b6.isSome = true ∧ l.b7.isSome = true ∧ l.b8.isSome = true

theorem Lane.full_after_tick {Body : Type} (l : Lane Body)
    (f : Body → Body) (new : Passenger Body) (h : l.full) :
    (l.tick f new).full := by
  rcases h with ⟨h3, h4, h5, h6, h7, h8⟩
  simp [Lane.tick, Lane.full, Option.isSome, *] at *

structure Network (Body : Type) where
  a : Lane Body := {}
  b : Lane Body := {}
  completed : Nat := 0

def Network.tick {Body : Type} (f : Body → Body)
    (seed : Nat → Bool → Body) (net : Network Body) : Network Body :=
  let n := net.completed
  { a := net.a.tick f ⟨2*n, n, seed n false⟩
    b := net.b.tick f ⟨2*n+1, n, seed n true⟩
    completed := n+1 }

def run {Body : Type} (f : Body → Body) (seed : Nat → Bool → Body) :
    Nat → Network Body
  | 0 => {}
  | n+1 => (run f seed n).tick f seed

theorem run_succ {Body : Type} (f : Body → Body)
    (seed : Nat → Bool → Body) (n : Nat) :
    run f seed (n+1) = (run f seed n).tick f seed := rfl

theorem run_completed {Body : Type} (f : Body → Body)
    (seed : Nat → Bool → Body) (n : Nat) :
    (run f seed n).completed = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [run_succ, Network.tick, ih]

theorem run_pair_arrival {Body : Type} (f : Body → Body)
    (seed : Nat → Bool → Body) (n : Nat) :
    ((run f seed (n+1)).a.b3.map Passenger.id) = some (2*n) ∧
    ((run f seed (n+1)).b.b3.map Passenger.id) = some (2*n+1) := by
  simp [run_succ, Network.tick, run_completed, Lane.tick]

theorem run_ids_length {Body : Type} (f : Body → Body)
    (seed : Nat → Bool → Body) (n : Nat) :
    (run f seed n).a.ids.length = n ∧
    (run f seed n).b.ids.length = n := by
  induction n with
  | zero => simp [run, Lane.ids]
  | succ n ih =>
      rcases ih with ⟨ha, hb⟩
      simp [run_succ, Network.tick, Lane.ids_tick, run_completed, ha, hb]

def passengerId (n : Nat) (side : Bool) : Nat :=
  2*n + if side then 1 else 0

theorem passengerId_injective (n m : Nat) (a b : Bool)
    (h : passengerId n a = passengerId m b) : n=m ∧ a=b := by
  cases a <;> cases b <;> simp [passengerId] at h ⊢ <;> omega

theorem Network.ids_tick {Body : Type} (f : Body → Body)
    (seed : Nat → Bool → Body) (net : Network Body) :
    (net.tick f seed).a.ids = (2*net.completed) :: net.a.ids ∧
    (net.tick f seed).b.ids = (2*net.completed+1) :: net.b.ids := by
  simp [Network.tick, Lane.ids_tick]

theorem full_at_six {Body : Type} (f : Body → Body)
    (seed : Nat → Bool → Body) :
    (run f seed 6).a.full ∧ (run f seed 6).b.full := by
  simp [run, Network.tick, Lane.tick, Lane.full]

theorem full_after_six {Body : Type} (f : Body → Body)
    (seed : Nat → Bool → Body) (n : Nat) :
    (run f seed (6+n)).a.full ∧ (run f seed (6+n)).b.full := by
  induction n with
  | zero => simpa using full_at_six f seed
  | succ n ih =>
      have step : 6+(n+1) = (6+n)+1 := by omega
      rw [step, run_succ]
      exact ⟨Lane.full_after_tick _ _ _ ih.1,
             Lane.full_after_tick _ _ _ ih.2⟩

#print axioms run_completed
#print axioms run_pair_arrival
#print axioms run_ids_length
#print axioms passengerId_injective
#print axioms Network.ids_tick
#print axioms full_after_six

end Chapter7PipelineCore
