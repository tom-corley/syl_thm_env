import Mathlib.Data.Nat.Prime
import Mathlib.GroupTheory.Sylow

open scoped Classical

variable (p : ℕ) [Fact p.Prime] (q : ℕ) [Fact q.Prime] (G : Type*) [Group G] [Fintype G]

theorem intersection_trivial (P : Sylow p G) (Q : Sylow q G) (hG: Fintype.card G = pq) (hp: Fintype.card P = p)
(hq: Fintype.card Q = q) (hp1: P.Normal) (hq1: Q.Normal) : (P : Subgroup G) ⊓ (Q : Subgroup G) = ⊥ := by
  sorry
