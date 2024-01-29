
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
theorem C_pq (q : ℕ) [hp : Fact p.Prime] [hq : Fact q.Prime] (hdvd: p<q ∧ Fintype.card G = p*q) (h:¬(p ∣ q - 1)): IsCyclic G := by
   have P : Subgroup G := by exact Subgroup.center G
   have Q : Subgroup G := by exact Subgroup.center G
   have h0 : p ∣ Fintype.card G := by
      rw [hdvd.2]
      exact Nat.dvd_mul_right p q
   have S1 P : Sylow p G := by exact P
   have h1 : q ∣ Fintype.card G := by
      rw [hdvd.2]
      exact Nat.dvd_mul_left q p
   have S2 Q : Sylow q G := by exact Q

   have O :


   done
