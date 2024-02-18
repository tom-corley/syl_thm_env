import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.Data.Finset.Card
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Data.Nat.Prime
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Coset
import Mathlib.GroupTheory.GroupAction.Defs

open scoped Classical

variable (p : ℕ) [Fact p.Prime] (q : ℕ) [Fact q.Prime] (G : Type*) [Group G] [Fintype G]

theorem hh (hG: Fintype.card G = 20) : Fintype.card (⊤ : Subgroup G) = 20 := by
  rw [Fintype.card_eq]
  have :  (⊤ : Subgroup G) = G := by apply?



theorem rf (P : Subgroup G) (hp : Fintype.card P = 5) (hg :Fintype.card (⊤ : Subgroup G) = 20) :  Fintype.card P ≠ Fintype.card (⊤ : Subgroup G) := by
  rw [hp, hg]
  decide

theorem d (P : Subgroup G) (hp: Fintype.card P ≠ Fintype.card (⊤ : Subgroup G) ) : P ≠ ⊤ := by exact ne_of_apply_ne (fun P => Fintype.card { x // x ∈ P }) hp
