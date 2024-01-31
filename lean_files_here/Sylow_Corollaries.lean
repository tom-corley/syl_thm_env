
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

open scoped Classical

variable (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [Fintype G]

-- Cauchy's Theorem 1 - G contains an element of order p
theorem Cauchy_1 (hdvd : p ∣ Fintype.card G) : ∃ g : G, orderOf g = p := by
   exact exists_prime_orderOf_dvd_card p hdvd
   done

theorem Cauchy_12 (hdvd : p ∣ Fintype.card G) : ∃ g : G, orderOf g = p := by
   have P := Sylow p G

   done

-- A group of order pq for primes p and q and such that p doesn't divide q-1, is the cyclic group of pq elements
theorem C_pq (q : ℕ) [hp : Fact (Nat.Prime p)] [hq : Fact q.Prime] (hpq: p<q) (hpqq: Fintype.card G = p*q) (h:¬(p ∣ q - 1)): IsCyclic G := by
--Define the Sylow p-subgroup
  have p0 : p ∣ Fintype.card G := by
    rw [hpqq]
    exact Nat.dvd_mul_right p q
  have p1 := Sylow.exists_subgroup_card_pow_prime p ((pow_one p).symm ▸ p0)
  rw [pow_one] at p1
  obtain ⟨P, hP⟩ := by exact p1
--Define the Sylow q-subgroup
  have q0 : q ∣ Fintype.card G := by
    rw [hpqq]
    exact Nat.dvd_mul_left q p
  have q1 := Sylow.exists_subgroup_card_pow_prime q ((pow_one q).symm ▸ q0)
  rw [pow_one] at q1
  obtain ⟨Q, hQ⟩ := by exact q1
--Show the Sylow p-subgroup is normal
  --have p2 : Fintype.card (Sylow p G) = 1 := by
    --apply exists_eq_mul_left_of_dvd(Nat.ModEq.dvd(card_sylow_modEq_one p G)) by

  have p3 : IsCyclic P := by
    exact isCyclic_of_prime_card hP

  have q3 : IsCyclic Q := by
    exact isCyclic_of_prime_card hQ

  have p4 : CommGroup P := by exact IsCyclic.commGroup

  have q4 : CommGroup Q := by exact IsCyclic.commGroup
  





  sorry
