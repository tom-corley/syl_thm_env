
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

variable (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [Fintype G]

-- Cauchy's Theorem 1 - G contains an element of order p
theorem Cauchy_1 (hdvd : p ∣ Fintype.card G) : ∃ g : G, orderOf g = p := by
   exact exists_prime_orderOf_dvd_card p hdvd
   done

theorem Cauchy_12 (hdvd : p ∣ Nat.card G) : ∃ g : G, orderOf g = p := by
   have P := Sylow p G
   sorry
   done

theorem unique_of_normal [Finite (Sylow p G)] (P : Sylow p G)
(h : (P : Subgroup G).Normal) : Unique (Sylow p G) := by
    refine { uniq := fun Q ↦ ?_ }
    obtain ⟨x, h1⟩ := MulAction.exists_smul_eq G P Q
    obtain ⟨x, h2⟩ := MulAction.exists_smul_eq G P default
    rw [Sylow.smul_eq_of_normal] at h1 h2
    rw [← h1, ← h2]
    done



-- A group of order pq for primes p and q and such that p doesn't divide q-1, is the cyclic group of pq elements
theorem C_pq (q : ℕ) [hp : Fact p.Prime] [hq : Fact q.Prime] (hpq: p<q) (hpqq: Fintype.card G = p*q) (h:¬(p ∣ q - 1)): IsCyclic G := by
--Define the Sylow p-subgroup
  have p0 : p ∣ Fintype.card G := by
    rw [hpqq]
    exact Nat.dvd_mul_right p q
  have p1 := Sylow.exists_subgroup_card_pow_prime p ((pow_one p).symm ▸ p0)
  rw [pow_one] at p1
  obtain ⟨P, hP⟩ := by exact p1

  have p111 : ∃ P : Sylow p G, Fintype.card P = p := by
    sorry
--Show that the Sylow p-subgroup is unique
  have p11 : (P : Subgroup G).index = q :=
      --Subgroup.card_mul_index
      sorry

  have p1 : Fintype.card (Sylow p G) ∣ q := by
    -- apply card_sylow_dvd_index P
    sorry

--Define the Sylow q-subgroup
  have q0 : q ∣ Fintype.card G := by
    rw [hpqq]
    exact Nat.dvd_mul_left q p
  have q1 := Sylow.exists_subgroup_card_pow_prime q ((pow_one q).symm ▸ q0)
  rw [pow_one] at q1
  obtain ⟨Q, hQ⟩ := by exact q1





--Show the Sylow p-subgroup is normal
  --have p2 : Nat.card (Sylow p G) = 1 := by
   --apply exists_eq_mul_left_of_dvd(Nat.ModEq.dvd(card_sylow_modEq_one p G))

 -- have p3 : IsCyclic P := by
 --  exact isCyclic_of_prime_card hP

 -- have q3 : IsCyclic Q := by
  --  exact isCyclic_of_prime_card hQ

--  have p4 : CommGroup P := by exact IsCyclic.commGroup

 -- have q4 : CommGroup Q := by exact IsCyclic.commGroup

 -- have p5: Subgroup.Normal P := by sorry

 -- have q5: Subgroup.Normal Q := by sorry




  -- Show the Sylow p-subgroup is normal
-- First, let's prove that P is a subgroup of G
---have p5: Subgroup G := ⟨P, hP.1⟩

-- Next, we'll show that P is normal in G
  have p6: Subgroup.Normal P  := by
  {
    apply Sylow.conjugate_subgroup
    exact hP.2
  }








  sorry
