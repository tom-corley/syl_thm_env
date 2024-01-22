/-
GENERAL COMMENTS:
This file is our first attempt at formalizing the Sylow Theorems and their consequences. We included it to show our progress throughout the project and to share the difficulties we faced by commenting on the relevant sections. The main issues that caused us problems were finiteness and type classes.

Normally, if a group is finite, then its subgroups would also be finite. This means that a Sylow p-subgroup is finite and a subgroup. However, Lean does not naturally understand this. Instead, Lean will complain, “failed to synthesize instance Fintype” or that the types didn’t match when comparing to another subgroup and using built-in tactics for subgroups. A partial solution that we found was to use coercion, which helped Lean understand that a Sylow p-subgroup is also a subgroup.

When we wrote our definitions and got them to a point where Lean wouldn’t directly complain to us, we thought the definition was correct. However, we were very wrong about this. The definition was clearly wrong as when we tried implementing it into theorems and proofs, Lean presented us with more errors, mostly being about the type class. This is why we have so many different definitions for a p-subgroup and for conjugation (we did not manage to define conjugation).
-/

-- ====================
-- ===== Imports ======
-- ====================

import Mathlib.Data.ZMod.Basic -- includes definition of modular equality; for example used in Sylow_4 theorem
import Mathlib.GroupTheory.Index -- includes definition of index of a group; for example used in the sylow_card_eq_index_normalizer theorem
import Mathlib.Data.Finset.Card -- includes definition of finite cardinality; for example used in Sylow_1 theorem
import Mathlib.GroupTheory.OrderOfElement -- includes definition of order of an element of a group; for example used in p_subgroup_3 definition
import Mathlib.Data.Nat.Choose.Dvd --  includes Nat.Prime.dvd_choose theorem; for example used in lemma binomial_coefsadf_prop2 proposition
import Mathlib.Data.Nat.Choose.Basic -- includes the Nat.choose function, which computes the binomial coefficients; for example used in binomial_coeff_prop1 proposition
import Mathlib.Algebra.Group.Defs -- includes definition of a group; for example used in Cauchy_1 theorem
import Mathlib.GroupTheory.Subgroup.Basic -- includes definition of a subgroup and normal subgroup; for example used in the sylow_subgroup_normality
import Mathlib.GroupTheory.SpecificGroups.Cyclic -- includes definition of a cyclic group; for example used in theorem C_pq
import Mathlib.Data.Nat.Prime -- includes definition of a prime number; for example used in variables

-- ======================
-- === Basic examples ===
-- ======================

-- We incorporate the following to verify if the functions we discovered are the ones we require and are performing effectively.

#eval 5 ≡ 8 [MOD 3]

example : 5 ≡ 8 [MOD 3] := by
rfl

#eval Nat.choose 5 2

example: Nat.choose 4 2 = 6 := by
rfl
done

-- ========================
-- ===== Definitions ======
-- ========================

section Definitions

-- p is a prime, G is a finite group
variable (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [Fintype G] -- decided to define variable first so we don't have to


-- ** Defining a finite p-group : A finite group of order p^n for some natural n, where p is prime

def p_subgroup: Prop := -- Original definition from Sylow.lean (Mathlib) which we try to redefine as this one is only valid if G is specified to be finite set as otherwise vector spaces of uncountable dimension over Z/pZ integers modulo p are finite p-groups according to this definition
  ∀ g : G, ∃ k : ℕ, g ^ p ^ k = 1

def p_subgroup_2 : Prop := -- somehow this definition didn't work when we tried using it in Sylow structure at first as we got error "failed to synthesize instance Fintype { x // x ∈ toSubgroup }" which required us to include the noncomputable instance below
  ∃ n : ℕ, Fintype.card G = p ^ n

noncomputable instance (H : Subgroup G) : Fintype {x // x ∈ H} := by
  sorry
  done

def p_subgroup_3 : Prop := -- the other option we came up with for all elements in G, there exists n, such that the order is p^n
  ∀ g : G, ∃ n : ℕ, orderOf g = p^n

-- Typecheck
#check p_subgroup_3

-- ** Defining a Sylow p-group, a p-group where the power of p is maximal
/-- A Sylow `p`-subgroup is a maximal `p`-subgroup. -/
structure Sylow extends Subgroup G where
  p_subgroup_3' : p_subgroup_2 p toSubgroup
  is_maximal' : ∀ {Q : Subgroup G}, p_subgroup_2 p Q → toSubgroup ≤ Q → Q = toSubgroup

-- This instance allows us to seamlessly treat a Sylow subgroup of a group G as a subgroup of G without needing to specify the conversion explicitly each time, which was initially overlooked as a necessity.
instance : CoeOut (Sylow p G) (Subgroup G) :=
  ⟨Sylow.toSubgroup⟩

end Definitions

section Preliminary_Results

-- =====================================
-- === Necessary preliminary results ===
-- =====================================

variable (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [Fintype G]

-- proof sketch: Prove that the set Syl_p(G) of Sylow p-subgroups of a finite group G, is finite
noncomputable instance (G: Type*) [Fintype G] [Group G] : Fintype (Subgroup G) := by
  apply Fintype.ofInjective (u-    : Subgroup G → Set G)
  intros A B
  exact SetLike.ext'

-- Defining the property that a subgroup is a Sylow-p subgroup
def issylow (K : Subgroup G) : Prop := -- this one didn't work in the Sylow Thm about existence
∀ k : K, ∃ n : ℕ, orderOf k = p ^ n ∧ ∀ (Q : Subgroup G), p_subgroup_3 p Q → K ≤ Q → Q = K

-- Define the conjugate subgroup of H by g

-- if p prime divides order of G then G has at least one Sylow p-subgroup
theorem existence_one (hdvd : p ∣ Fintype.card G) (Q : Subgroup G) : Q=Sylow p G:= by
  sorry
  done

end Preliminary_Results

section Sylow_1_Necessary_Lemmas_Wielandt

variable (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [Fintype G]

--The following Lemmas will help when we

-- Lemma 3.3 page 36 Intro to Group Theory i)
lemma binomial_coefsadf_prop1 (i : ℕ) (hp : p.Prime) (h : 1 ≤ i ∧ i < p) : p ∣ Nat.choose p i := by
  hp.dvd_choose h.right (Nat.sub_lt_of_pos_le h.left (le_of_lt h.right)) (le_refl _)
  done

-- typecheck
#check binomial_coefseff_prop1

-- Lemma 3.3 page 36 Intro to Group Theory ii)
lemma binomial_coefseff_prop2 {n m : ℕ} (hp : Nat.gcd m p = 1) : Nat.choose (m * p ^ n) (p ^ n) ≡ m [MOD p] := by
  sorry
  done

-- typecheck
#check binomial_coefsadf_prop2

end Sylow_1_Necessary_Lemmas_Wielandt

section Sylow_2_and_3_Necessary_Props

-- === Attempts at Conjugation for Sylow thms 2 & 3 ===
-- *************************

variable (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [Fintype G]

-- if x is an element of G, and H is a sylow p-subgroup of G, subgroup G??
def conjugate123 (x : G) (H : Sylow p G) : Subgroup G :=
  { carrier := {a : G | ∃ h ∈ H.carrier, a = x * h * x⁻¹},
    one_mem' := by sorry,
    mul_mem' := by sorry,
    inv_mem' := by sorry
  }

-- Defining the conjugacy action?
def ConjAct2312 (Q : Subgroup G) (x : G) (H : Sylow p G) : Subgroup G :=
{
  carrier := {a ∈ Q.carrier | ∃ h ∈ H.carrier, a = x * h * x⁻¹},
  one_mem' :=
  }
  mul_mem' := by sorry,
  inv_mem' := by sorry
}

--Proposition 3.5 page 39 Intro to Group Theory I don't how to write gPg^-1 so that lean understands
theorem notsuire (hdvd : p ∣ Fintype.card G) (H : Subgroup G) (P : Sylow p G): Subgroup.subgroupOf H ((P : Subgroup G).ConjAct2312) ∈ (Sylow p H):= by
  sorry
  done

theorem notsuirse (hdvd : p ∣ Fintype.card G) (H : Subgroup G) (P : Sylow p G) :
∃ (Q : Sylow p H), Q.carrier = ConjAct2312 P := by
  sorry
  done

def normalCore (H : Subgroup G) (Q : Sylow p G): Subgroup G where
  carrier := { a : G | ∀ b : G, b * a * b⁻¹ ∈ H }
  one_mem' a := by rw [mul_one, mul_inv_self]; exact H.one_mem
  inv_mem' {a} h b := (congr_arg (· ∈ H) conj_inv).mp (H.inv_mem (h b))
  mul_mem' {a b} ha hb c := (congr_arg (· ∈ H) conj_mul).mp (H.mul_mem (ha c) (hb c))

def ConjAct22312 (Q : Subgroup G) (x : G) (H : Sylow p G) : Subgroup G :=
{
  carrier := {a ∈ Q.carrier | ∃ h ∈ H.carrier, a = x * h * x⁻¹},
  one_mem' := by sorry,
  mul_mem' := by sorry,
  inv_mem' := by sorry
}

def normalCsore (H: Sylow p G) : Subgroup G where
  carrier := { a : G | ∀ b : G, b * a * b⁻¹ ∈ (H : Subgroup G) }
  one_mem' a := by rw [mul_one, mul_inv_self]; exact H.one_mem
  inv_mem' {a} h b := (congr_arg (· ∈ (H : Subgroup G) ) conj_inv).mp (H.inv_mem (h b))
  mul_mem' {a b} ha hb c := (congr_arg (· ∈ (H : Subgroup G) ) conj_mul).mp (H.mul_mem (ha c) (hb c))


#check binomial_coefsadf_prop2
#check Sylow p G

end Sylow_2_and_3_Necessary_Props

section Sylow_Theorems_Proofs
-- ===================================
-- ====== Sylow's Theorems 1-4 =======
-- ===================================

variable (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [Fintype G]

-- Sylows 1st Theorem: (Existence of a Sylow p-subgroup in G)
-- if p prime divides order of G then G has at least one Sylow p-subgroup
theorem Sylow_1 (hdvd : p ∣ Fintype.card G) (Q: Subgroup G) : Sylow p Q := by
-- hypotheses: p divides order of G, Q is a subgroup in G?
  sorry
  done

#check card_sylow_modEq_one


-- lemma sylow_2 [fintype G] {p : ℕ} (hp : nat.prime p)
--   (H K : set G) [Sylow H hp] [Sylow K hp] :
--   ∃ g : G, H = conjugate_set g K :=
--
-- theorem Sylow_2 [fintype G] [hp nat.prime p] [P,K : Sylow p G] : ∃g ∈ G P = gKg^-1

-- Sylow's 3rd Theorem: If P is a p-subgroup of G, It is contained in a Sylow p-subgroup of G
theorem Sylow_3 (P : Subgroup G) (hP : p_subgroup p P) : ∃ Q : Sylow p G, P ≤ Q := by
  sorry
  done

-- Sylow's 4th Theorem, number of Sylow p-subgroups is congruent to 1 mod p
theorem Sylow_4 [Fintype (Sylow p G)] : Fintype.card (Sylow p G) ≡ 1 [MOD p] := by
  sorry
  done

end Sylow_Theorems_Proofs

section Sylow_Consequences

-- ==========================================
-- ===== CONSEQUENCES OF SYLOWS THEOREMS ====
-- ==========================================

variable (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [Fintype G]

-- Corollary 3.7(i) page 40
theorem sylow_card_eq_index_normalizer (hdvd : p ∣ Fintype.card G) (P : Sylow p G) [Fintype (Sylow p G)] : Fintype.card (Sylow p G) = Subgroup.index (normalCsore (P : Subgroup G)) := by
  sorry
  done

-- #check sylow_card_eq_index_normalizer

-- Corollary 3.7(ii)
-- If p divides the order of G, and P is a Sylow p-subgroup of G, number of Sylow p-subgroups divides |G|/|G|_p
theorem sylow_card_divides_group_order_div_sylow_order (hdvd : p ∣ Fintype.card G) (P : Sylow p G) [Fintype P] [Fintype (Sylow p G)] : Fintype.card (Sylow p G) ∣ (Fintype.card G / Fintype.card P) := by
  sorry
  done

#check sylow_card_divides_group_order_div_sylow_order

-- Corollary 3.7(iii)
-- If p divides the order of G, and P is a Sylow p-subgroup of G, P is normal if and only if there is exactly one Sylow p-subgroup
theorem sylow_subgroup_normality_condition (hdvd : p ∣ Fintype.card G) (P : Sylow p G) [Fintype P] [Fintype (Sylow p G)] : (P : Subgroup G).Normal ↔ Fintype.card (Sylow p G) = 1 := by
  sorry
  done

#check sylow_subgroup_normality_condition

-- p divides the number of Sylow p subgroups -1 (where in notes???)
theorem card_sylow_modEq_one_new [Fintype (Sylow p G)] : p ∣ Fintype.card (Sylow p G) -1 := by
  sorry
  done

-- ======================
-- === Other Theorems ===
-- ======================

-- Theorem 2.22. (Cauchy’s theorem) Let G be a finite group, and let p be a prime divisor of |G|. Then G contains an element of order p. In fact, the number of elements of G of orderp is congruent to −1 modulo p.

theorem Cauchy_1 (hdvd : p ∣ Fintype.card G) : ∃ g : G, orderOf g = p := by
  sorry
  done

theorem Cauchy_2 (hdvd : p ∣ Fintype.card G) (H : Set G) [Fintype H] (hgh : ∀ h : H, ∃ g : G, h=g ∧ orderOf g = p): Fintype.card H ≡ p-1 [MOD p] := by
  sorry
  done

-- Classifying families of groups: Lemma 4.14
-- For a group G of order pq, where p andq are distinct primes and q is not congruent to 1 (mod p), the groupG is isomorphic to Cpq
theorem C_pq (q : ℕ) [Fact q.Prime] (hdvd: p<q ∧ Fintype.card G = p*q) (h:¬(p ∣ q - 1)): IsCyclic G := by
  sorry
  done

end Sylow_Consequences

section Sylow_Game
-- =========================
-- ====== SYLOW GAME =======
-- =========================

variable (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [Fintype G]

--Let G be a group of order 20. Can G be simple?

-- Example for order 20:
lemma sylow_five_subgroup_exists [Fact (Fintype.card G = 20)] [h : Fact (5 ∣ Fintype.card G)] : ∃ H : Subgroup G, Fintype.card H = 5 ∧ Sylow 5 H := by
  sorry
  done

-- theorem existence_one_five (hdvd : 5 ∣ Fintype.card G) (Q: Subgroup G): Sylow 5 Q := by
-- apply existence_one
-- apply hdvd
-- done

theorem sylow_card_divides_group_order_div_sylow_order_five (hdvd: 5 ∣ Fintype.card G) (hG: Fintype.card G =20) [Fintype (Sylow 5 G)] (P : Sylow 5 G) (hP: Fintype P ): Fintype.card (Sylow 5 G) ∣ (Fintype.card G / 5) := by
  sorry
  done

theorem sylow_card_divides_group_worder_div_sylow_order_five [Fact (Fintype.card G = 20)] [h : Fact (5 ∣ Fintype.card G)]  (P : Sylow 5 G) [Fintype P] [Fintype (Sylow 5 G)] : Fintype.card (Sylow 5 G) ∣ 4 := by
refine (Nat.ord_compl_dvd_ord_compl_iff_dvd (Fintype.card (Sylow 5 G)) 4).mp ?_
  sorry
  done

example (hG : Fintype.card G = 20) [Fintype (Sylow 5 G)] (P: Subgroup G)  [Fintype P]: ¬ IsSimpleGroup G := by
  have h₀ : Nat.Prime 5 := by norm_num
  have h₁ : Fintype.card G = 2^2 * 5 :=  by linarith [hG]
  have h₂ : 5 ∣ (Fintype.card G) := by use 4
  obtain ⟨P, hP⟩ : Sylow 5 P:= by exact Sylow_1 5 G h₂ P
  have h_3 : Fintype.card (Sylow 5 P) = 5 := by apply?
  have h₂ : Fintype.card (Sylow 5 G) ≡ 1 [MOD 5] := by exact card_sylow_modEq_one 5 G
  have h_6 : Fintype.card (Sylow 5 G) ∣ (Fintype.card G / Fintype.card P) := by sorry

  end Sylow_Game
