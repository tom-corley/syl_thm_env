import Mathlib.Data.Nat.Prime
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Subgroup.Simple

open scoped Classical

variable (p : ℕ) [Fact p.Prime] (q : ℕ) [Fact q.Prime] (G : Type*) [Group G] [Fintype G]

example (hG : Fintype.card G = 20) (Q: Subgroup G) (h: Q.Normal): ¬ IsSimpleGroup G := by
  have h1 : Q ≠ ⊥ := by sorry

  have h2 : Q ≠ ⊤ := by sorry

  intro h3
  have := h3.eq_bot_or_eq_top_of_normal Q h
  cases this <;> contradiction -- `exact this.elim h1 h2` will also work here
  done
