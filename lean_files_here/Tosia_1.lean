
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
import Mathlib.Logic.Unique
import Mathlib.Init.Set

open scoped Classical

variable (p : ℕ) [Fact p.Prime] (q : ℕ) [Fact q.Prime] (G : Type*) [Group G] [Fintype G]

variable {H : Subgroup G}

theorem card_sylow_eq_one_unique_sylow [Finite (Sylow p G)] (h1: Fintype.card (Sylow p G) = 1) : Nonempty (Unique (Sylow p G)) := by
-- Fintype.card_eq_one_iff_nonempty_unique.mp h1
  exact Fintype.card_eq_one_iff_nonempty_unique.mp h1

def card_sylow_eq_one_unique_sylow_def [Finite (Sylow p G)] (h1: Fintype.card (Sylow p G) = 1) (P : Sylow p G) : Unique (Sylow p G) :=
letI := Fintype.card_le_one_iff_subsingleton.mp h1.le
uniqueOfSubsingleton P

-- If G has a unique Sylow p-subgroup P, then it is normal in G
theorem normal_of_unique [Finite (Sylow p G)] (P : Sylow p G)
(h : Fintype.card (Sylow p G) = 1) : (P : Subgroup G).Normal := 


theorem  whatever (hpq: p<q) [hp : Fact p.Prime] [hq : Fact q.Prime] : ¬ (q∣ p) := by
  refine Nat.not_dvd_of_pos_of_lt ?h1 hpq
  exact Fin.size_pos'
  done

-- theorem card_sylow_eq_index_normalizer [Fact p.Prime] [Fintype (Sylow p G)] (P : Sylow p G) :
    -- card (Sylow p G) = (P : Subgroup G).normalizer.index :=

theorem card_eq_one_unique (α : Type u) (h1: Cardinal.mk α = 1): Subsingleton α := by



theorem Subsingleton.unique {α : Sort u} [h : Subsingleton α] (a : α) : Unique α := by
  exact uniqueOfSubsingleton a

theorem dskan [Fintype G] {p : ℕ} [Fact p.Prime] (H : Subgroup G) [Fintype H]
    (card_eq : Fintype.card H = p ^ (Fintype.card G).factorization p) : Sylow p G := by
  exact Sylow.ofCard H card_eq

theorem card_eq_one_unique (α : Type u) [Fintype α] (h1: Fintype.card α = 1): NonEmpty (Unique α) := by
  sorry

theorem mk_eq_one (α : Type u) [Fintype α] (h1: Fintype.card α = 1) : (Unique α) := by
 rw [Cardinal.eq_one_iff_unique]
 doneCardinal.eq_one_iff_unique



theorem card_sylow_eq_one_unique_sylow [Finite (Sylow p G)] (h1: Fintype.card (Sylow p G) = 1) (P : Sylow p G) : Unique (Sylow p G) := by
  sorry

theorem unique_element_of_card_one {A : Type} {s : Set A} [Fintype s] (h1: Fintype.card s = 1 ) (x : s):
  ∃! x, x ∈ s := by sorry




theorem exists_unique_sylow_subgroup_of_cardinality_one
  (h : Fintype.card (Sylow p G) = 1) : ∃ P : Sylow p G, True := by
   exact (exists_const (Sylow p G)).mpr trivial

theorem shswshs [Finite (Sylow q G)] (h1: Fintype.card (Sylow q G) = 1) (q0 : q ∣ Fintype.card G ): Unique (Sylow q G) := by
  have dn :  ¬ (Fintype.card (Sylow q G) > 1) := by
     exact Eq.not_lt (id h1.symm)
  have dn3 : Fintype.card (Sylow q G) ≠ 0 := by
    exact Fintype.card_ne_zero
  have q1 := Sylow.exists_subgroup_card_pow_prime q ((pow_one q).symm ▸ q0)
  rw [pow_one] at q1
  refine { uniq := fun Q ↦ ?_ }
  obtain ⟨x, h1⟩ := MulAction.exists_smul_eq G P Q
  obtain ⟨x, h2⟩ := MulAction.exists_smul_eq G P default
  rw [Sylow.smul_eq_of_normal] at h1 h2
  rw [← h1, ← h2]






  done

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
theorem pq_normal_sylow_q_subgroup [hp : Fact p.Prime] [hq : Fact q.Prime] [Finite (Sylow p G)]
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
    have p1 : 1 < p := by exact p0
    exact Nat.sub_pos_of_lt p0

-- Go through the cases we got in h4 to show which one is true
  cases h4 with
  | inl h => exact h
  | inr h => rw [h] at h1
             exact (h6 h1).elim

  apply Nat.not_eq_zero_of_lt h



  done
