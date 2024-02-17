
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

variable {H : Subgroup G}

-- Took this theorem from Mathlib.GroupTheory.OrderOfElement.
-- We use it in our proof to show groups of order pq are cyclic. This theorem works in the online
-- editor but since it is fairly new it wouldn't work from the import.
lemma orderOf_coe (a : H) : orderOf (a : G) = orderOf a :=
  orderOf_injective H.subtype Subtype.coe_injective _

-- Cauchy's Theorem - G contains an element of order p
theorem Cauchy (hdvd : p ∣ Fintype.card G) : ∃ g : G, orderOf g = p := by
   exact exists_prime_orderOf_dvd_card p hdvd

-- The following theorem tells us that Sylow p-subgroup normal in G implies that it is the unique Sylow p-subgroup
theorem unique_of_normal [Finite (Sylow p G)] (P : Sylow p G)
(h : (P : Subgroup G).Normal) : Unique (Sylow p G) := by
    refine { uniq := fun Q ↦ ?_ }
    obtain ⟨x, h1⟩ := MulAction.exists_smul_eq G P Q
    obtain ⟨x, h2⟩ := MulAction.exists_smul_eq G P default
    rw [Sylow.smul_eq_of_normal] at h1 h2
    rw [← h1, ← h2]

-- If G has a unique Sylow p-subgroup P, then it is normal in G
theorem normal_of_unique [Finite (Sylow p G)] (P : Sylow p G)
(h : Fintype.card (Sylow p G) = 1) : (P : Subgroup G).Normal := by
  sorry

-- If G is order pq such that p < q, then G has a unique Sylow q-subgroup
theorem pq_unique_sylow_q_subgroup [hp : Fact p.Prime] [hq : Fact q.Prime] [Finite (Sylow p G)]
(Q : Sylow q G) (h : p<q) (hG: Fintype.card G = p*q) : Fintype.card (Sylow q G) = 1 := by
-- The Sylow q-subgroup has order q
  have q0 : q ∣ Fintype.card G := by
    rw [hG]
    exact Nat.dvd_mul_left q p
  have q1 := Sylow.exists_subgroup_card_pow_prime q ((pow_one q).symm ▸ q0)
  rw [pow_one] at q1
  have q2 : Fintype.card (Q : Subgroup G) = q := by
    have pp : p.Prime := Fact.out
    have qp : q.Prime := Fact.out
    rw [Sylow.card_eq_multiplicity]
    convert pow_one _
    rw [hG]
    rw [Nat.factorization_mul_apply_of_coprime ((Nat.coprime_primes pp qp).mpr h.ne)]
    rw [Nat.factorization_eq_zero_of_lt h]
    rw [qp.factorization_self]

-- Number of Sylow q-subgroups is congruent to 1 MOD q
  have h1 : 1 ≡ Fintype.card (Sylow q G) [MOD q] := by
    exact Nat.ModEq.symm (card_sylow_modEq_one q G)
  rw [Nat.modEq_iff_dvd'] at h1

-- Number of Sylow q-subgroups divide the index |G:Q|
  have h2 : Fintype.card (Sylow q G) ∣ (Q : Subgroup G).index := by
    exact card_sylow_dvd_index Q

-- Index |G:Q| is equal to p
  have h3 : Fintype.card G = (Q : Subgroup G).index * Fintype.card Q := by
    exact (Subgroup.index_mul_card (Q : Subgroup G)).symm
  rw [hG, q2, mul_left_inj'] at h3

  rw [← h3] at h2

-- Using what we have the only possible values are 1 and p
  have h4 : Fintype.card (Sylow q G) = 1 ∨ Fintype.card (Sylow q G) = p := by
    refine Nat.Prime.eq_one_or_self_of_dvd ?pp (Fintype.card (Sylow q G)) h2
    exact hp.1

-- Using that p < q, we have h1 cannot hold if number of Sylow q-subgroups is p
  have h5 : p-1 < q := by exact tsub_lt_of_lt h
  have h6 : ¬ (q ∣ p - 1) := by
    refine Nat.not_dvd_of_pos_of_lt ?h1 h5
    have p0 : 2 ≤ p := by exact Nat.Prime.two_le hp.1
    exact Nat.sub_pos_of_lt p0

-- Go through the cases we got in h4 to show which one is true
  cases h4 with
  | inl h => exact h
  | inr h => rw [h] at h1
             exact (h6 h1).elim

  apply Nat.not_eq_zero_of_lt h

  have h7: Fintype.card (Sylow q G) ≠ 0 := by
    exact Fintype.card_ne_zero
  exact Nat.one_le_iff_ne_zero.mpr h7

  done


-- If G is order pq such that p doesn't divide q-1, then G has a unique Sylow p-subgroup
theorem pq_unique_sylow_p_subgroup [hp : Fact p.Prime] [hq : Fact q.Prime] [Finite (Sylow p G)] (P : Sylow p G)
(h : p < q) (hh : ¬(p ∣ q - 1)) (hG: Fintype.card G = p*q) : Fintype.card (Sylow p G) = 1 := by
-- p does not divide q
  have p_not_dvd_q : ¬ (p ∣ q) := by
    have cpq : Nat.Coprime p q := by
      have p_not_q : p ≠ q := by exact Nat.ne_of_lt h
      exact (Nat.coprime_primes hp.1 hq.1).2 p_not_q
    exact (Nat.Prime.coprime_iff_not_dvd hp.1).1 cpq

-- The Sylow p-subgroup has order p
  have p0 : p ∣ Fintype.card G := by
    rw [hG]
    exact Nat.dvd_mul_right p q
  have p1 := Sylow.exists_subgroup_card_pow_prime p ((pow_one p).symm ▸ p0)
  rw [pow_one] at p1
  have p2 : Fintype.card (P : Subgroup G) = p := by
    have pp : p.Prime := Fact.out
    have qp : q.Prime := Fact.out
    rw [Sylow.card_eq_multiplicity]
    convert pow_one _
    rw [hG]
    rw [Nat.factorization_mul_apply_of_coprime ((Nat.coprime_primes pp qp).mpr h.ne)]
    rw [Nat.Prime.factorization_self]
    rw [Nat.factorization_eq_zero_of_not_dvd]
    apply p_not_dvd_q
    exact hp.1

-- Number of Sylow p-subgroups is congruent to 1 MOD p
  have h1 : 1 ≡ Fintype.card (Sylow p G) [MOD p] := by
    exact Nat.ModEq.symm (card_sylow_modEq_one p G)
  rw [Nat.modEq_iff_dvd'] at h1

-- Number of Sylow p-subgroups divide the index |G:P|
  have h2 : Fintype.card (Sylow p G) ∣ (P : Subgroup G).index := by
    exact card_sylow_dvd_index P

-- Index |G:Q| is equal to q
  have h3 : Fintype.card G = (P : Subgroup G).index * Fintype.card P := by
    exact (Subgroup.index_mul_card (P : Subgroup G)).symm
  rw [hG, p2, mul_comm, mul_left_inj'] at h3

  rw [← h3] at h2

-- Using what we have the only possible values are 1 and q
  have h4 : Fintype.card (Sylow p G) = 1 ∨ Fintype.card (Sylow p G) = q := by
    refine Nat.Prime.eq_one_or_self_of_dvd ?pp (Fintype.card (Sylow p G)) h2
    exact hq.1

  cases h4 with
  | inl h => exact h
  | inr h => rw [h] at h1
             exact (hh h1).elim

  exact NeZero.ne p

  have h5: Fintype.card (Sylow p G) ≠ 0 := by
    exact Fintype.card_ne_zero
  exact Nat.one_le_iff_ne_zero.mpr h5

-- A group of order pq for primes p and q and such that p doesn't divide q-1, is the cyclic group of pq elements
theorem C_pq (q : ℕ) [hp : Fact p.Prime] [hq : Fact q.Prime] [lp : Finite (Sylow p G)] (hpq: p<q)
(hpqq: Fintype.card G = p*q) (h:¬(p ∣ q - 1)): IsCyclic G := by
-- Define the Sylow p-subgroup
  have p0 : p ∣ Fintype.card G := by
    rw [hpqq]
    exact Nat.dvd_mul_right p q
  have p1 := Sylow.exists_subgroup_card_pow_prime p ((pow_one p).symm ▸ p0)
  rw [pow_one] at p1
  obtain ⟨P, hP⟩ := p1
-- Show P is cyclic and generated by an element g of order p
  have p3 : IsCyclic P := by
    exact isCyclic_of_prime_card hP
  obtain ⟨g, gP⟩ := IsCyclic.exists_generator (α := P)
  have p4 : orderOf g = Fintype.card P := by exact orderOf_eq_card_of_forall_mem_zpowers gP

-- Define the Sylow q-subgroup
  have q0 : q ∣ Fintype.card G := by
    rw [hpqq]
    exact Nat.dvd_mul_left q p
  have q1 := Sylow.exists_subgroup_card_pow_prime q ((pow_one q).symm ▸ q0)
  rw [pow_one] at q1
  obtain ⟨Q, hQ⟩ := q1
-- Show Q is cyclic and generated by an element k of order q
  have q3 : IsCyclic Q := by
    exact isCyclic_of_prime_card hQ
  obtain ⟨k, kQ⟩ := IsCyclic.exists_generator (α := Q)
  have q4 : orderOf k = Fintype.card Q := by exact orderOf_eq_card_of_forall_mem_zpowers kQ

-- Show p and q are coprime
  have pq_coprime : Nat.gcd p q = 1 := by
   refine (Nat.coprime_primes ?pp ?pq).mpr ?_
   apply hp.1
   apply hq.1
   exact Nat.ne_of_lt hpq

-- The Sylow p-subgroup P is unique and hence normal

  have p5 : Fintype.card (Sylow p G) = 1 := by
    apply pq_unique_sylow_p_subgroup p q
    sorry
    apply hpq
    apply h
    apply hpqq

  have p6 : (↑P : Subgroup G).Normal := by
    apply normal_of_unique p P



-- Show g and k commute
  have g_k_commute : Commute (g : G) (k : G) := by sorry

-- Show gh generates G ie gh has order pq
  have pq : Nat.Coprime (orderOf (g : G)) (orderOf (k : G)) → orderOf (g * k : G) = orderOf (g : G) * orderOf (k : G) := by
    exact Commute.orderOf_mul_eq_mul_orderOf_of_coprime g_k_commute
-- Rewrite this statement so we can use it
  rw [orderOf_coe, orderOf_coe, p4, q4, hP, hQ] at pq

-- Show that the order of G matches the order of gk
  have order : Fintype.card G = orderOf (g* k : G) := by
    rw [hpqq, pq]
    apply pq_coprime

-- Finally we can use the fact that G contains an element which has order pq, so it must generate G
  exact isCyclic_of_orderOf_eq_card (↑g * ↑k) (id order.symm)





--Show that the Sylow p-subgroup is unique
  have pp3 : Subgroup.index P = q := by
    sorry

  have pp4 : Fintype.card (Sylow p G) ∣ q := by
    sorry

  have pp5 : Fintype.card (Sylow p G) ≡ 1 [MOD p] := by
    exact card_sylow_modEq_one p G

  have pp6 : Fintype.card (Sylow p G) = 1 := by
    sorry

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


-- review of your code (KB)
-- (KB) for problem at the very end, it seems to be fixed by using `Finite` instead of `Fintype`.
variable (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [Finite G]

-- (KB) Your comment below should be a *docstring*, so start with `/--`, finish with `-/`
-- A group of order pq for primes p and q and such that p doesn't divide q-1, is the cyclic group of pq elements
theorem C_pqKB (q : ℕ) [hp : Fact p.Prime] [hq : Fact q.Prime] (hdvd: p<q ∧ Nat.card G = p*q) (h:¬(p ∣ q - 1)): IsCyclic G := by
-- Define the Sylow p-subgroup
  have h0 : Fintype G := by
    exact Fintype.ofFinite (G)
  have h1 : p ∣ Nat.card G := by
    rw [hdvd.2]
    exact Nat.dvd_mul_right p q
  have h2 := Sylow.exists_subgroup_card_pow_prime p ((pow_one p).symm ▸ h1)
  rw [pow_one] at p1
  obtain ⟨P, hP⟩ := by exact p1
