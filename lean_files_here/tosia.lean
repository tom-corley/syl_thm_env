import Mathlib.GroupTheory.Sylow
import Mathlib.Data.Finset.Card
import Mathlib.Data.ZMod.Basic -- Contains definition of modular equality
import Mathlib.GroupTheory.Index -- Contains definition of group index
import Mathlib.GroupTheory.Subgroup.Basic -- Contains definition of a normal subgroup
import Mathlib.Data.Nat.Prime -- Contains definition of a prime
import Mathlib.Data.Nat.ModEq

import Mathlib.Data.Nat.Factorization.Basic -- Roshan import this


variable (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [Fintype G]


-- The example states that a group of order 20 cannot be simple
example (hG : Fintype.card G = 20) : ¬ IsSimpleGroup G := by
  -- Establish that 5 is a prime number
  have h1 : Fact (Nat.Prime 5) := fact_iff.mpr (by norm_num)

  -- Prove that 5 divides the order of the group G
  have h₂ : 5 ∣ Fintype.card G := by use 4 -- 5 divides 20 (20 = 4 * 5)

  have h3 : 20 = 4*5 := by exact rfl

  -- Apply Sylow's theorem to conclude the existence of a Sylow 5-subgroup
  -- The theorem guarantees a subgroup of order 5^1, as 5 is a prime dividing the group's order
  have h₃ := Sylow.exists_subgroup_card_pow_prime 5 <| (pow_one 5).symm ▸ h₂

  -- We extract the actual subgroup Q which satisfies the Sylow p-subgroup conditions for p=5
  obtain ⟨Q, hQ⟩ := h₃

  have h₄: Fintype Q := Fintype.ofFinite Q

  have h₅: (Nat.factorization 20) 5 = 1 := by
    rw [h3, Nat.factorization_mul_apply_of_coprime]
    norm_num
    rw [Nat.factorization_eq_zero_of_lt]
    apply Nat.lt.base 4
    exact rfl

  have card_eq : Fintype.card Q = 5 ^ (Nat.factorization (Fintype.card G)) 5 := by
    rw [hG]
    convert hQ

  have S := Sylow.ofCard Q card_eq

  -- Now we use Sylow's theorems to analyse the number of such subgroups

   -- Use Sylow's theorems to deduce the number of Sylow p-subgroups is congruent to 1 mod p
  have h₄ : Fintype.card (Sylow 5 G) ≡ 1 [MOD 5] := card_sylow_modEq_one 5 G

  -- Show that the number of Sylow 5-subgroups divides the order of the group divided by the order of a Sylow 5-subgroup
  have h₅ : (Fintype.card (Sylow 5 G)) ∣ (Fintype.card G)/(Fintype.card Q) := by sorry
  have h₆ : Fintype.card (Sylow 5 G) = 1 ∨ Fintype.card (Sylow 5 G) = 4 := by sorry
  have h₇ : ¬ (4 ≡ 1 [MOD 5]) := by
    -- intro h
    -- contradiction
    decide

  -- Establish that there is exactly one Sylow 5-subgroup in G

  have h₈ : Fintype.card (Sylow 5 G) = 1 := by sorry

  -- Conclude the existence and uniqueness of the Sylow 5-subgroup, implying it is normal
  -- The uniqueness of the Sylow subgroup follows from h₈ and the properties of Sylow subgroups
  obtain ⟨P, hP⟩ := Fintype.card_eq_one_iff.mp h₈

  -- Prove that the unique Sylow subgroup P is a normal subgroup of G
  -- This will use the fact that a unique Sylow subgroup is always normal
  have h₁₀ : Subgroup.Normal Q := by sorry

  -- Conclude that G is not simple because it has a normal subgroup of order 5
  -- This final step uses the definition of a simple group, which cannot have non-trivial normal subgroups
  exact h₁₀


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
