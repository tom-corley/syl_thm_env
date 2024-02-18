
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
  have coprime_p_q : Nat.Coprime p q := by
      have p_not_q : p ≠ q := by exact Nat.ne_of_lt hpq
      exact (Nat.coprime_primes hp.1 hq.1).2 p_not_q

-- p does not divide q
  have p_not_dvd_q : ¬ (p ∣ q) := by
      exact (Nat.Prime.coprime_iff_not_dvd hp.1).1 coprime_p_q

-- q does not divide p
  have q_not_dvd_p : ¬ (q∣ p) := by
    refine (Nat.Prime.coprime_iff_not_dvd ?pp).mp ?_
    exact hq.1
    exact Nat.Coprime.symm coprime_p_q

-- We want lean to consider P as a Sylow p subgroup so we can apply our earlier theorems

  have p5 : Fintype.card P = p ^ (Fintype.card G).factorization p := by
    rw [hP, hpqq]
    have p6 : (Nat.factorization (p * q)) p = 1 := by
      rw [Nat.factorization_mul_apply_of_coprime ((Nat.coprime_primes hp.1 hq.1).mpr hpq.ne)]
      rw [Nat.Prime.factorization_self]
      rw [Nat.factorization_eq_zero_of_not_dvd]
      apply p_not_dvd_q
      exact hp.1
    rw [p6, pow_one]

  have P : Sylow p G := by exact Subgroup_to_Sylow G P p5

-- Showing that P is the unique Sylow p-subgroup and hence it is normal in G

  have p7 : Fintype.card (Sylow p G) = 1 := by
    apply pq_unique_sylow_p_subgroup p q
    exact P
    exact hpq
    exact h
    exact hpqq

  have p8 : (P : Subgroup G).Normal := by
    exact normal_of_sylow_card_eq_one p G P p7

-- We want lean to consider Q as a Sylow q subgroup so we can apply our earlier theorems

  have q5 : Fintype.card Q = q ^ (Fintype.card G).factorization q := by
    rw [hQ, hpqq]
    have q6 : (Nat.factorization (p * q)) q = 1 := by
      rw [Nat.factorization_mul_apply_of_coprime ((Nat.coprime_primes hp.1 hq.1).mpr hpq.ne)]
      rw [Nat.Prime.factorization_self]
      rw [Nat.factorization_eq_zero_of_not_dvd]
      exact q_not_dvd_p
      exact hq.1
    rw [q6, pow_one]

  have Q : Sylow q G := by exact Subgroup_to_Sylow G Q q5

-- Showing that Q is the unique Sylow q-subgroup and hence it is normal in G

  have q7 : Fintype.card (Sylow q G) = 1 := by
    apply pq_unique_sylow_q_subgroup p q
    exact Q
    exact hpq
    exact hpqq

  have q8 : (Q : Subgroup G).Normal := by
    exact normal_of_sylow_card_eq_one q G Q q7

-- P and Q have trivial intersection

  have intersection_trivial : (P : Subgroup G) ⊓ (Q : Subgroup G) = ⊥ := by sorry

-- gkg^(-1)k^(-1) lies in both P and Q so must be the identity element

  have hP_normal : (k*g⁻¹*k⁻¹ : G) ∈ P := by sorry

  have in_P : (g*k*g⁻¹*k⁻¹ : G) ∈ P := by sorry

  have in_Q : (g*k*g⁻¹*k⁻¹ : G) ∈ Q := by sorry

  have is_id : (g*k*g⁻¹*k⁻¹ : G) = 1 := by sorry

-- Show g and k commute
  have g_k_commute : Commute (g : G) (k : G) := by
    exact commutatorElement_eq_one_iff_commute.mp is_id

-- Show gh generates G ie gh has order pq
  have pq : Nat.Coprime (orderOf (g : G)) (orderOf (k : G)) → orderOf (g * k : G) = orderOf (g : G) * orderOf (k : G) := by
    exact Commute.orderOf_mul_eq_mul_orderOf_of_coprime g_k_commute
-- Rewrite this statement so we can use it
  rw [orderOf_coe, orderOf_coe, p4, q4, hP, hQ] at pq

-- Show that the order of G matches the order of gk
  have order : Fintype.card G = orderOf (g* k : G) := by
    rw [hpqq, pq]
    apply coprime_p_q

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


--==================================================================================
--                                   SYLOW GAME
--==================================================================================

-- The example states that a group of order 20 cannot be simple
example (hG : Fintype.card G = 20) : ¬ IsSimpleGroup G := by
  -- Establish that 5 is a prime number
  have h1 : Fact (Nat.Prime 5) := fact_iff.mpr (by norm_num)

  -- Prove that 5 divides the order of the group G
  have h₂ : 5 ∣ Fintype.card G := by use 4 -- 5 divides 20 (20 = 4 * 5)

  have h3 : 20 = 4*5 := by exact rfl

  -- Apply Sylow's theorem to conclude the existence of a Sylow 5-subgroup
  -- The theorem guarantees a subgroup of order 5^1, as 5 is a prime dividing the group's order
  have h₃ := Sylow.exists_subgroup_card_pow_prime 5 ((pow_one 5).symm ▸ h₂)
  rw [pow_one] at h₃

  -- We extract the actual subgroup Q which satisfies the Sylow p-subgroup conditions for p=5
  obtain ⟨Q, hQ⟩ := h₃



  --have h₄: Fintype Q := Fintype.ofFinite Q

  have h₅: (Nat.factorization 20) 5 = 1 := by
    rw [h3, Nat.factorization_mul_apply_of_coprime]
    norm_num
    rw [Nat.factorization_eq_zero_of_lt]
    apply Nat.lt.base 4
    exact rfl

  have card_eq : Fintype.card Q = 5 ^ (Fintype.card G).factorization 5 := by
    rw [hG, hQ, h₅, pow_one]

-- REMEMBER TO DELETE IF NOT USED
 -- have S := Sylow.ofCard Q card_eq

  have ff : Fintype.card G = (Q : Subgroup G).index * Fintype.card (Q : Subgroup G) := by exact (Subgroup.index_mul_card ↑Q).symm
  rw [hG, hQ, h3, mul_left_inj'] at ff

  have Q : Sylow 5 G := by exact Subgroup_to_Sylow G Q card_eq

  -- Now we use Sylow's theorems to analyse the number of such subgroups

   -- Use Sylow's theorems to deduce the number of Sylow p-subgroups is congruent to 1 mod p
  have h₄ : Fintype.card (Sylow 5 G) ≡ 1 [MOD 5] := card_sylow_modEq_one 5 G

  -- Show that the number of Sylow 5-subgroups divides the order of the group divided by the order of a Sylow 5-subgroup
  have h₅ : (Fintype.card (Sylow 5 G)) ∣ (Q : Subgroup G).index := by exact card_sylow_dvd_index Q

  have h₆ : (Fintype.card (Sylow 5 G) = 1) ∨ (Fintype.card (Sylow 5 G) = 4) := by sorry -- THIS NEED TO BE PROVED


  have h₇ : ¬ (4 ≡ 1 [MOD 5]) := by
    -- intro h
    -- contradiction
    decide

  -- Establish that there is exactly one Sylow 5-subgroup in G

  have h8 : Fintype.card (Sylow 5 G) = 1 := by
    cases h₆ with
    | inl h => exact h
    | inr h => rw [h] at h₄
               exact (h₇ h₄).elim


  -- Prove that the unique Sylow subgroup P is a normal subgroup of G
  -- This will use the fact that a unique Sylow subgroup is always normal
  have h₁₀ : (Q : Subgroup G).Normal := by exact normal_of_sylow_card_eq_one 5 G Q h8

  -- Conclude that G is not simple because it has a normal subgroup of order 5
  have h1 : (Q : Subgroup G) ≠ ⊥ := by exact Sylow.ne_bot_of_dvd_card Q h₂

  have h2 : (Q : Subgroup G) ≠ ⊤ := by sorry -- THIS NEED TO BE PROVED

  intro h3
  have := h3.eq_bot_or_eq_top_of_normal Q h₁₀
  cases this <;> contradiction -- `exact this.elim h1 h2` will also work here

  exact Nat.succ_ne_zero 4

  done

















-- The example states that a group of order 462 cannot be simple
example (hG : Fintype.card G = 36) : ¬ IsSimpleGroup G := by
  -- Establish that 11 is a prime number
  have h1 : Fact (Nat.Prime 3) := fact_iff.mpr (by norm_num)

  -- Prove that 11 divides the order of the group G
  have h₂ : 3 ∣ Fintype.card G := by use -- 11 divides 462 (462 = 11 * 42)

  have h3 : 462 = 11*42 := by exact rfl

  have h4: 42 = 2 *21 := by exact rfl

  have h5: 21 = 3 *7 := by exact rfl

  -- Apply Sylow's theorem to conclude the existence of a Sylow 5-subgroup
  -- The theorem guarantees a subgroup of order 5^1, as 5 is a prime dividing the group's order
  have h₃ := Sylow.exists_subgroup_card_pow_prime 11 <| (pow_one 11).symm ▸ h₂

  -- We extract the actual subgroup Q which satisfies the Sylow p-subgroup conditions for p=11
  obtain ⟨Q, hQ⟩ := h₃

  have h₄: Fintype Q := Fintype.ofFinite Q

  have h₅: (Nat.factorization 462) 11 = 1 := by
    rw [h3, Nat.factorization_mul_apply_of_coprime]
    norm_num
    rw [h4, Nat.factorization_mul_apply_of_coprime
    norm_num
    rw [h5, Nat.factorization_mul_apply_of_coprime]
    norm_num
    apply rfl
    apply rfl
    exact rfl

  have card_eq : Fintype.card Q = 11 ^ (Nat.factorization (Fintype.card G)) 11 := by
    rw [hG]
    convert hQ

  have S := Sylow.ofCard Q card_eq

  -- Now we use Sylow's theorems to analyse the number of such subgroups

   -- Use Sylow's theorems to deduce the number of Sylow p-subgroups is congruent to 1 mod p
  have h₄ : Fintype.card (Sylow 11 G) ≡ 1 [MOD 11] := card_sylow_modEq_one 11 G

  -- Show that the number of Sylow 5-subgroups divides the order of the group divided by the order of a Sylow 5-subgroup
  have h₅ : (Fintype.card (Sylow 5 G)) ∣ (Fintype.card G)/(Fintype.card Q) := by sorry
  have h₆ : Fintype.card (Sylow 5 G) = 1 ∨ Fintype.card (Sylow 5 G) = 42 := by sorry
  have h₇ : ¬ (42 ≡ 1 [MOD 11]) := by
    -- intro h
    -- contradiction
    decide

  -- Establish that there is exactly one Sylow 11-subgroup in G

  have h₈ : Fintype.card (Sylow 11 G) = 1 := by sorry

  -- Conclude the existence and uniqueness of the Sylow 11-subgroup, implying it is normal
  -- The uniqueness of the Sylow subgroup follows from h₈ and the properties of Sylow subgroups
  obtain ⟨P, hP⟩ := Fintype.card_eq_one_iff.mp h₈

  -- Prove that the unique Sylow subgroup P is a normal subgroup of G
  -- This will use the fact that a unique Sylow subgroup is always normal
  have h₁₀ : Subgroup.Normal Q := by sorry

  -- Conclude that G is not simple because it has a normal subgroup of order 11
  -- This final step uses the definition of a simple group, which cannot have non-trivial normal subgroups
  exact h₁₀
