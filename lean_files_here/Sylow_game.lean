
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
--                                   SYLOW GAME
--==================================================================================

-- We show that a group of order 20 cannot be simple relying on the Sylow file and "Key results" Section in the beginning of the file
example (hG : Fintype.card G = 20) : ¬ IsSimpleGroup G := by
  -- Establish that 5 is a prime number
  have h1 : Fact (Nat.Prime 5) := fact_iff.mpr (by norm_num)

  -- Prove that 5 divides the order of the group G
  have h2 : 5 ∣ Fintype.card G := by use 4 -- 5 divides 20 (20 = 4 * 5)

  -- Write the equation |G| = m * p^n where p prime and gcd(p,m) = 1 but with |G| = 20, m = 4, p = 5 and n = 1
  have h3 : 20 = 4 * 5 := by exact rfl

  -- Apply Sylow's theorem to conclude the existence of a Sylow 5-subgroup
  -- The theorem ensures a Sylow 5-subgroup of order 5^1, given 5 - a prime that divides the group's order at its highest power of 5
  have h4 := Sylow.exists_subgroup_card_pow_prime 5 ((pow_one 5).symm ▸ h2)
  rw [pow_one] at h4

  -- We extract the actual subgroup Q which satisfies the Sylow p-subgroup conditions for p=5
  obtain ⟨Q, hQ⟩ := h4

  -- Show that in the prime factorisation of 20, 5 appears exactly once.
  have h5: (Nat.factorization 20) 5 = 1 := by
    rw [h3, Nat.factorization_mul_apply_of_coprime]
    norm_num
    rw [Nat.factorization_eq_zero_of_lt]
    apply Nat.lt.base 4
    exact rfl

  have card_eq : Fintype.card Q = 5 ^ (Fintype.card G).factorization 5 := by
    rw [hG, hQ, h5, pow_one]

  -- Show that the index of Q in G is equal to 4
  have h6 : Fintype.card G = (Q : Subgroup G).index * Fintype.card (Q : Subgroup G) := by exact (Subgroup.index_mul_card ↑Q).symm
  rw [hG, hQ, h3, mul_left_inj'] at h6

  have Q : Sylow 5 G := by exact Subgroup_to_Sylow G Q card_eq

  -- Now we use Sylow's theorems to analyse the number of such subgroups

   -- Use Sylow's theorems to deduce the number of Sylow p-subgroups is congruent to 1 mod p
  have h7 : Fintype.card (Sylow 5 G) ≡ 1 [MOD 5] := card_sylow_modEq_one 5 G

  -- Show that the number of Sylow 5-subgroups divides the index of Q in G
  have h8 : (Fintype.card (Sylow 5 G)) ∣ (Q : Subgroup G).index := by exact card_sylow_dvd_index Q

  -- Establish that the cardinality of the set of Sylow 5-subgroups of G can only be either equal to 1 or 4
  have h9 : (Fintype.card (Sylow 5 G) = 1) ∨ (Fintype.card (Sylow 5 G) = 4) := by sorry -- THIS NEED TO BE PROVED

  -- Show that 4 is not congruent to 1 mod 5
  have h10 : ¬ (4 ≡ 1 [MOD 5]) := by
    decide


  -- Establish that there is exactly one Sylow 5-subgroup in G
  have h11 : Fintype.card (Sylow 5 G) = 1 := by
    cases h9 with
    | inl h => exact h
    | inr h => rw [h] at h7
               exact (h10 h7).elim

  -- Prove that the unique Sylow subgroup P is a normal subgroup of G
  -- This will use the fact that a unique Sylow subgroup is always normal
  have h12 : (Q : Subgroup G).Normal := by exact normal_of_sylow_card_eq_one 5 G Q h11

  -- Conclude that G is not simple because it has a normal subgroup of order 5
  -- This conclusion relies on demonstrating that Q, as a subgroup of G, is neither trivial nor G itself
  have h13 : (Q : Subgroup G) ≠ ⊥ := by exact Sylow.ne_bot_of_dvd_card Q h2

  have h14 : (Q : Subgroup G) ≠ ⊤ := by apply?

  intro h
  have := h.eq_bot_or_eq_top_of_normal Q h12
  cases this <;> contradiction -- could also use `exact this.elim h1 h2`

  -- Resolve the remaining subgoals
  exact Nat.succ_ne_zero 4

  done


-- We repeat the same reasoning to show that the group of order 462 is not simple
example (hG : Fintype.card G = 462) : ¬ IsSimpleGroup G := by
  -- Establish that 11 is a prime number
  have h1 : Fact (Nat.Prime 11) := fact_iff.mpr (by norm_num)

  -- Prove that 11 divides the order of the group G
  have h2 : 11 ∣ Fintype.card G := by use 42 -- 11 divides 462 (462 = 11 * 42)

  have h3 : 462 = 42 * 11:= by exact rfl

  have h4: 42 = 2 *21 := by exact rfl

  have h5: 21 = 3 *7 := by exact rfl

  -- Apply Sylow's theorem to conclude the existence of a Sylow 11-subgroup
-- The theorem ensures a Sylow 11-subgroup of order 11^1, given 11 - a prime that divides the group's order at its highest power of 11
  have h6 := Sylow.exists_subgroup_card_pow_prime 11 <| (pow_one 11).symm ▸ h2

  -- We extract the actual subgroup Q which satisfies the Sylow p-subgroup conditions for p equal to 11
  obtain ⟨Q, hQ⟩ := h6

  -- Show that in the prime factorisation of 20, 5 appears exactly once.
  have h7: (Nat.factorization 462) 11 = 1 := by
    rw [h3, Nat.factorization_mul_apply_of_coprime]
    norm_num
    rw [h4, Nat.factorization_mul_apply_of_coprime]
    norm_num
    rw [h5, Nat.factorization_mul_apply_of_coprime]
    norm_num
    apply rfl
    apply rfl
    exact rfl

  have card_eq : Fintype.card Q = 11 ^ (Nat.factorization (Fintype.card G)) 11 := by
    rw [hG]
    convert hQ

  -- Show that the index of Q in G is equal to 42
  have h6 : Fintype.card G = (Q : Subgroup G).index * Fintype.card (Q : Subgroup G) := by exact (Subgroup.index_mul_card ↑Q).symm
  rw [hG, hQ, h3, pow_one, mul_left_inj'] at h6

  have Q : Sylow 11 G := by exact Subgroup_to_Sylow G Q card_eq

  -- Now we use Sylow's theorems to analyse the number of such subgroups

   -- Use Sylow's theorems to deduce the number of Sylow p-subgroups is congruent to 1 mod p
  have h9 : Fintype.card (Sylow 11 G) ≡ 1 [MOD 11] := card_sylow_modEq_one 11 G

  -- Show that the number of Sylow 11-subgroups divides the index of Q in G
  have h10 : (Fintype.card (Sylow 11 G)) ∣ (Q : Subgroup G).index := by exact card_sylow_dvd_index Q

-- Establish that the cardinality of the set of Sylow 5-subgroups of G can only be either equal to 1 or 4
  have h11 : Fintype.card (Sylow 11 G) = 1 ∨ Fintype.card (Sylow 11 G) = 42 := by sorry

-- Show that 4 is not congruent to 1 mod 5
  have h12 : ¬ (42 ≡ 1 [MOD 11]) := by
    decide

-- Establish that there is exactly one Sylow 11-subgroup in G
  have h13 : Fintype.card (Sylow 11 G) = 1 := by
    cases h11 with
    | inl h => exact h
    | inr h => rw [h] at h9
               exact (h12 h9).elim

  -- Prove that the unique Sylow subgroup P is a normal subgroup of G
  -- This will use the fact that a unique Sylow subgroup is always normal
  have h12 : (Q : Subgroup G).Normal := by exact normal_of_sylow_card_eq_one 11 G Q h13

  -- Conclude that G is not simple because it has a normal subgroup of order 5
  -- This conclusion relies on demonstrating that Q, as a subgroup of G, is neither trivial nor G itself
  have h13 : (Q : Subgroup G) ≠ ⊥ := by exact Sylow.ne_bot_of_dvd_card Q h2

  have h14 : (Q : Subgroup G) ≠ (⊤ : Subgroup G) := by
    have hb: Fintype.card (Q : Subgroup G) = 5 := by
      rw[]
    have ha : Fintype.card (⊤ : Subgroup G) = 20 := by sorry
    have hp : Fintype.card (Q : Subgroup G) ≠ Fintype.card (⊤ : Subgroup G) := by
      rw [hQ, ha]
      decide
    exact ne_of_apply_ne (fun Q => Fintype.card { x // x ∈ Q}) hp



  intro h
  have := h.eq_bot_or_eq_top_of_normal Q h12
  exact this.elim h13 h14

  -- Resolve the remaining subgoals
  exact Nat.succ_ne_zero 10

  done
