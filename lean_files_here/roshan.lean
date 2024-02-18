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

theorem mul (g k : G) (hg : g ∈ P) (hk : k ∈ Q) (hP : (P : Subgroup G).Normal)
(hQ : (Q : Subgroup G).Normal) : (g*k*g⁻¹*k⁻¹ : G) ∈ P := by
  rw [mul_assoc, mul_assoc]
  refine Subgroup.mul_mem P hg ?_
  rw [← mul_assoc]
  refine Subgroup.Normal.conj_mem hP g⁻¹ ?_ k
  exact Subgroup.inv_mem P hg



variable (p : ℕ) [Fact p.Prime] (q : ℕ) [Fact q.Prime] (G : Type*) [Group G] [Fintype G]

theorem bigtheorem (P : Sylow p G) (Q : Sylow q G) : IsCyclic G := by

-- obtain the generator of P and say P is normal
  have p3 : IsCyclic P := by sorry
  obtain ⟨g, gP⟩ := IsCyclic.exists_generator (α := P)
  have p8 : (P : Subgroup G).Normal := by sorry

-- obtain the generator of Q and say Q is normal
  have q3 : IsCyclic Q := by sorry
  obtain ⟨k, kQ⟩ := IsCyclic.exists_generator (α := Q)
  have q8 : (Q : Subgroup G).Normal := by sorry

-- what I am having trouble proving given my previous post
  have in_P : (g*k*g⁻¹*k⁻¹ : G) ∈ P := by
    simp_rw [mul_assoc (g : G)]
    apply P.mul_mem g.prop
    apply p8.conj_mem
    apply P.inv_mem g.prop


  sorry
