import Mathlib.Data.Nat.Prime
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Subgroup.Simple

open scoped Classical

variable (p : ℕ) [Fact p.Prime] (q : ℕ) [Fact q.Prime] (G : Type*) [Group G] [Fintype G]

example (hG : Fintype.card G = 20) (Q: Subgroup G) (N : Subgroup.normalizer G Q) (h: Q.Normal): ¬ IsSimpleGroup G := by
  have h1 : Q ≠ ⊥ := by sorry

  have h2 : Q ≠ ⊤ := by sorry
  cases
