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

--==================================================================================
--                                 KEY RESULTS
--==================================================================================

-- Took this theorem from Mathlib.GroupTheory.OrderOfElement.
-- We use it in our proof to show groups of order pq are cyclic. This theorem works in the online
-- editor but since it is fairly new it wouldn't work from the import.
lemma orderOf_coe (a : H) : orderOf (a : G) = orderOf a :=
  orderOf_injective H.subtype Subtype.coe_injective _

-- The following theorem is a definition in the Sylow.lean file
-- We put it here as we can use it to switch P from subgroup to Sylow p-subgroup
theorem Subgroup_to_Sylow [Fintype G] {p : ℕ} [Fact p.Prime] (H : Subgroup G) [Fintype H]
    (card_eq : Fintype.card H = p ^ (Fintype.card G).factorization p) : Sylow p G := by
  exact Sylow.ofCard H card_eq

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

-- If G has only one Sylow p-subgroup P, then it is normal in G
theorem normal_of_sylow_card_eq_one [Finite (Sylow p G)] (P : Sylow p G)
(h : Fintype.card (Sylow p G) = 1) : (P : Subgroup G).Normal := by
  rw [card_sylow_eq_index_normalizer P, Subgroup.index_eq_one, Subgroup.normalizer_eq_top] at h
  exact h

-- We found "unique_of_normal" in the Sylow.lean file and we wanted to provide a converse to it
-- Although we do not use the following theorem in our code below we wanted to provide it for
-- completion.
theorem normal_of_unique [Finite (Sylow p G)] (P : Sylow p G)
(h : Nonempty (Unique (Sylow p G))) : (P : Subgroup G).Normal := by
  rw [← Fintype.card_eq_one_iff_nonempty_unique] at h
  exact normal_of_sylow_card_eq_one _ _ P h

--==================================================================================
--              GROUPS OF ORDER pq ARE CYCLIC (GIVEN p DOESN'T DIVIDE q)
--==================================================================================

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

-- If G is order pq such that p < q, then the Sylow q-subgroup is normal

theorem pq_normal_sylow_q_subgroup [hp : Fact p.Prime] [hq : Fact q.Prime] [Finite (Sylow p G)] (Q : Sylow q G)
(h : p < q) (hG: Fintype.card G = p*q) : (Q : Subgroup G).Normal := by
  have h1 : Fintype.card (Sylow q G) = 1 := by exact pq_unique_sylow_q_subgroup p q G Q h hG
  exact normal_of_sylow_card_eq_one q G Q h1

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

-- If G is order pq such that p doesn't divide q-1, then the Sylow p-subgroup is normal

theorem pq_normal_sylow_p_subgroup [hp : Fact p.Prime] [hq : Fact q.Prime] [Finite (Sylow p G)] (P : Sylow p G)
(h : p < q) (hh : ¬(p ∣ q - 1)) (hG: Fintype.card G = p*q) : (P : Subgroup G).Normal := by
  have h1 : Fintype.card (Sylow p G) = 1 := by exact pq_unique_sylow_p_subgroup p q G P h hh hG
  exact normal_of_sylow_card_eq_one p G P h1

-- The following lemmas will be useful in the final theorem

-- Show p and q are coprime
theorem coprime_p_q (q : ℕ) [hp : Fact p.Prime] [hq : Fact q.Prime] (hpq: p<q) : Nat.Coprime p q := by
      have p_not_q : p ≠ q := by exact Nat.ne_of_lt hpq
      exact (Nat.coprime_primes hp.1 hq.1).2 p_not_q

-- p does not divide q
theorem p_not_dvd_q (q : ℕ) [hp : Fact p.Prime] [hq : Fact q.Prime] (hpq: p<q) : ¬ (p ∣ q) := by
      exact (Nat.Prime.coprime_iff_not_dvd hp.1).1 (coprime_p_q p q hpq)

-- q does not divide p
theorem q_not_dvd_p (q : ℕ) [hp : Fact p.Prime] [hq : Fact q.Prime] (hpq: p<q) : ¬ (q ∣ p) := by
    refine (Nat.Prime.coprime_iff_not_dvd ?pp).mp ?_
    exact hq.1
    exact Nat.Coprime.symm (coprime_p_q p q hpq)

-- A group of order pq for primes p and q and such that p doesn't divide q-1, is the cyclic group of pq elements
theorem C_pq (q : ℕ) [hp : Fact p.Prime] [hq : Fact q.Prime] (hpq: p<q)
(hpqq: Fintype.card G = p*q) (h:¬(p ∣ q - 1)): IsCyclic G := by

-- Define and obtain the Sylow p-subgroup
  have p0 : p ∣ Fintype.card G := by
    rw [hpqq]
    exact Nat.dvd_mul_right p q
  have p1 := Sylow.exists_subgroup_card_pow_prime p ((pow_one p).symm ▸ p0)
    rw [pow_one] at p1
    obtain ⟨P, hP⟩ := p1

-- We want lean to consider P as a Sylow p subgroup so we can apply our earlier theorems

have p5 : Fintype.card P = p ^ (Fintype.card G).factorization p := by
  rw [hP, hpqq]
  have p6 : (Nat.factorization (p * q)) p = 1 := by
    rw [Nat.factorization_mul_apply_of_coprime ((Nat.coprime_primes hp.1 hq.1).mpr hpq.ne)]
    rw [Nat.Prime.factorization_self]
    rw [Nat.factorization_eq_zero_of_not_dvd]
    apply p_not_dvd_q
    exact hpq
    exact hp.1
  rw [p6, pow_one]

have P : Sylow p G := by exact Subgroup_to_Sylow G P p5