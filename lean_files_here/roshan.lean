import Mathlib.Data.Nat.Prime
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Subgroup.Simple

open scoped Classical

variable (p : ℕ) [Fact p.Prime] (q : ℕ) [Fact q.Prime] (G : Type*) [Group G] [Fintype G]



--example (hG : Fintype.card G = 20) (Q: Subgroup G) (h: Q.Normal): ¬ IsSimpleGroup G := by
--  have h1 : Q ≠ ⊥ := by sorry
--
--  have h2 : Q ≠ ⊤ := by sorry
--  cases

variable (G : Type*) [Group G] [Fintype G] (P Q : Subgroup G)

theorem mul (g : P) (k : Q) (h : (P : Subgroup G) ⊓ (Q : Subgroup G) = ⊥) (hP : (P : Subgroup G).Normal)
(hQ : (Q : Subgroup G).Normal) : (g*k*g⁻¹*k⁻¹ : G) ∈ P := by
  exact?
