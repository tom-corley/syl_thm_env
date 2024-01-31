
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
  have h1 := Sylow.exists_subgroup_card_pow_prime p ((pow_one p).symm ▸ h0)
  rw [pow_one] at h1
  sorry
