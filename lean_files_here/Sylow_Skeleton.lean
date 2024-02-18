/-
GENERAL COMMENTS:
This file is our first attempt at formalizing the Sylow Theorems and their consequences. We included it to show our progress throughout the project and to share the difficulties we faced by commenting on the relevant sections. The main issues that caused us problems were finiteness and type classes.

Normally, if a group is finite, then its subgroups would also be finite. This means that a Sylow p-subgroup is finite and a subgroup. However, Lean does not naturally understand this. Instead, Lean will complain, “failed to synthesize instance Fintype” or that the types didn’t match when comparing to another subgroup and using built-in tactics for subgroups. A partial solution that we found was to use coercion, which helped Lean understand that a Sylow p-subgroup is also a subgroup.

When we wrote our definitions and got them to a point where Lean wouldn’t directly complain to us, we thought the definition was correct. However, we were very wrong about this. The definition was clearly wrong as when we tried implementing it into theorems and proofs, Lean presented us with more errors, mostly being about the type class. This is why we have so many different definitions for a p-subgroup and for conjugation (we did not manage to define conjugation).
-/

-- ====================
-- ===== Imports ======
-- ====================

import Mathlib.Data.ZMod.Basic --includes definition of modular equality
-- import Mathlib.GroupTheory.Index haven't used it yet but will when we talk about the index of a subgroup
import Mathlib.Data.ZMod.Basic -- includes definition of modular equality; for example used in Sylow_4 theorem
import Mathlib.GroupTheory.Index -- includes definition of index of a group; for example used in the sylow_card_eq_index_normalizer theorem
import Mathlib.Data.Finset.Card -- includes definition of finite cardinality; for example used in Sylow_1 theorem
import Mathlib.GroupTheory.OrderOfElement -- includes definition of order of an element of a group; for example used in p_subgroup_3 definition
import Mathlib.Data.Nat.Choose.Dvd --  includes Nat.Prime.dvd_choose theorem; for example used in lemma binomial_coeffs_prop1 proposition
import Mathlib.Data.Nat.Choose.Basic -- includes the Nat.choose function, which computes the binomial coefficients; for example used in binomial_coeff_prop1 proposition
import Mathlib.Algebra.Group.Defs -- includes definition of a group; for example used in Cauchy_1 theorem
import Mathlib.GroupTheory.Subgroup.Basic -- includes definition of a subgroup and normal subgroup; for example used in the sylow_subgroup_normality
import Mathlib.GroupTheory.SpecificGroups.Cyclic -- includes definition of a cyclic group; for example used in theorem C_pq
import Mathlib.Data.Nat.Prime -- includes definition of a prime number; for example used in variables
import Mathlib.Data.Fintype.Basic


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

-- DEFINITION OF GROUP AND SUBGROUP

/-
class Group (G : Type u) extends DivInvMonoid G where
  protected mul_left_inv : ∀ a : G, a⁻¹ * a = 1
#align group Group
-/

/-
structure Subgroup (G : Type*) [Group G] extends Submonoid G where
  /-- `G` is closed under inverses -/
  inv_mem' {x} : x ∈ carrier → x⁻¹ ∈ carrier
#align subgroup Subgroup
-/

section Definitions

-- p is a prime, G is a finite group
variable (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [Fintype G] -- decided to define variable first so we don't have to


-- ** Defining a finite p-group : A finite group of order p^n for some natural n, where p is prime


-- Proposition, that given a prime p and a group, G is a p_subgroup
def p_subgroup: Prop := -- Original definition from Sylow.lean (Mathlib) (PGroup.lean???)
=======
def p_subgroup: Prop := -- Original definition from Sylow.lean (Mathlib) which we try to redefine as this one is only valid if G is specified to be finite set as otherwise vector spaces of uncountable dimension over Z/pZ integers modulo p are finite p-groups according to this definition

  ∀ g : G, ∃ k : ℕ, g ^ p ^ k = 1

def p_subgroup_2 : Prop := -- somehow this definition didn't work when we tried using it in Sylow structure at first as we got error "failed to synthesize instance Fintype { x // x ∈ toSubgroup }" which required us to include the noncomputable instance below
  ∃ n : ℕ, Fintype.card G = p ^ n

noncomputable instance (H : Subgroup G) : Fintype {x // x ∈ H} := by
  sorry
  done

-- Proof that a subgroup of fintype group is fintype
noncomputable instance (G: Type*) [Fintype G] [Group G] : Fintype (Subgroup G) := by
  apply Fintype.ofInjective ((↑) : Subgroup G → Set G)
  intros A B
  exact SetLike.ext'

def p_subgroup_3 : Prop := -- the other option we came up with for all elements in G, there exists n, such that the order is p^n
  ∀ g : G, ∃ n : ℕ, orderOf g = p^n

-- Typecheck
#check p_subgroup_3

-- ** Defining a Sylow p-group, a p-group where the power of p is maximal
/-- A Sylow `p`-subgroup is a maximal `p`-subgroup. -/


-- Note that here, Subgroup G is not a single subgroup of G, but in fact the set of subgroups of G?
-- Extension of the structure subgroup, with two additional properties
structure Sylow extends Subgroup G where
  p_subgroup_3' : p_subgroup_3 p toSubgroup
  -- For all subgroups Q in G, If Q is a p subgroup,
  is_maximal' : ∀ {Q : Subgroup G}, p_subgroup_3 p Q → toSubgroup ≤ Q → Q = toSubgroup
=======
structure Sylow extends Subgroup G where
  p_subgroup_2' : p_subgroup_2 p toSubgroup
  is_maximal' : ∀ {Q : Subgroup G}, p_subgroup_2 p Q → toSubgroup ≤ Q → Q = toSubgroup


-- This instance allows us to seamlessly treat a Sylow subgroup of a group G as a subgroup of G without needing to specify the conversion explicitly each time, which was initially overlooked as a necessity.
instance : CoeOut (Sylow p G) (Subgroup G) :=
  ⟨Sylow.toSubgroup⟩

end Definitions

section Sylow_1_Necessary_Lemmas_Wielandt

variable (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [Fintype G]

-- Lemma 3.3 page 36 Intro to Group Theory i)

lemma binomial_coefsadf_prop1 (i : ℕ) (hp : p.Prime) (h : 1 ≤ i ∧ i < p) : p ∣ Nat.choose p i :=
  hp.dvd_choose h.right (Nat.sub_lt_of_pos_le h.left (le_of_lt h.right)) (le_refl _)
=======
-- We managed to prove this proposition without much difficulty. We made us of Mathlib.Data.Nat.Choose.Dvd, which allowed us to prove 3 inequalities instead
lemma binomial_coeffs_prop1 (i : ℕ) (hp : p.Prime) (h : 1 ≤ i ∧ i < p) : p ∣ Nat.choose p i := by
  exact hp.dvd_choose h.right (Nat.sub_lt_of_pos_le h.left (le_of_lt h.right)) (le_refl _)
]
  done

-- typecheck
#check binomial_coeffs_prop1

-- Lemma 3.3 page 36 Intro to Group Theory ii) probs doable
lemma binomial_coefsadf_prop2 (i : ℕ) (hp : p.Prime) (h : 1 ≤ i ∧ i < p) : p ∣ Nat.choose p i := by
  apply Nat.Prime.dvd_choose hp
  apply h.right
  sorry
  apply le_refl
  --apply le_refl
  done

lemma binomial_coefsadf_prop24 (i : ℕ) (hp : p.Prime) (h : 1 ≤ i ∧ i < p) : p ∣ Nat.choose p i := by
  sorry
  --linarith
=======
-- Lemma 3.3 page 36 Intro to Group Theory ii)
-- We did not make much progress on this proof. We first realised that it would be too difficult or maybe not possible to replicate the proof done in MA3K4. So instead we decided to try an induction argument. However this was also quite difficult for us to prove on paper let alone in lean.
lemma binomial_coeffs_prop2 {n m : ℕ} (hp : Nat.gcd m p = 1) : Nat.choose (m * p ^ n) (p ^ n) ≡ m [MOD p] := by
  sorry
  done

-- typecheck
#check binomial_coeffs_prop2

end Sylow_1_Necessary_Lemmas_Wielandt

section Sylow_2_and_3_Necessary_Props

-- === Attempts at Conjugation for Sylow thms 2 & 3 ===
-- *************************

variable (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [Fintype G]

-- Failed to define the conjugation action on P by G gPg^{-1}
def Conjugate {G : Type*} [Group G] (g : G) (P : Sylow p G) : Subgroup G:=
{
  carrier := {x | ∃ y ∈ P.carrier, x = g * y * g⁻¹},
  one_mem' := by sorry,
  mul_mem' := by sorry,
  inv_mem' := by sorry,
}

--Proposition 3.5 page 39 Intro to Group Theory we don't know how to write gPg^-1 so that lean understands
theorem prop35 {G : Type*} [Group G] [Fintype G] (hdvd : p ∣ Fintype.card G) (g : G) (P : Sylow p G): Sylow p (Conjugate g P) := by
  sorry
  done

end Sylow_2_and_3_Necessary_Props

section Sylow_Theorems

-- ===================================
-- ====== Sylow's Theorems 1-4 =======
-- ===================================

variable (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [Fintype G]

-- Sylows 1st Theorem: (Existence of a Sylow p-subgroup in G)
-- if p prime divides order of G then G has at least one Sylow p-subgroup
theorem Sylow_1 (hdvd : p ∣ Fintype.card G) (Q: Subgroup G) : Sylow p G := by
-- hypotheses: p divides order of G, Q is a subgroup in G?
=======
-- if p prime divides order of G then G has at least one Sylow p-subgroup; this theorem is incorrect as we realised playing Sylow game that it's consquence is just a defintion
theorem sylow_p_subgroup_exists_1 (hdvd : p ∣ Fintype.card G) (Q : Subgroup G) : Sylow p Q := by
  sorry
  done

-- here is our second attempt
theorem sylow_p_subgroup_exists_2 (hdvd : p ∣ Fintype.card G) : ∃ (Q : Sylow p G), true := by
 sorry
 done

-- We were not able to state Sylow 2 due to us failing to provide a correct definition for conjugation

-- theorem Sylow_2 [fintype G] [hp nat.prime p] [P,K : Sylow p G] : ∃g ∈ G P = gKg^-1

-- Sylow's 3rd Theorem: If P is a p-subgroup of G, It is contained in a Sylow p-subgroup of G
theorem Sylow_3 (P : Subgroup G) (hP : p_subgroup p P) : ∃ Q : Sylow p G, P ≤ Q := by
  sorry
  done

-- Sylow's 4th Theorem, number of Sylow p-subgroups is congruent to 1 mod p
theorem Sylow_4 [Fintype (Sylow p G)] : Fintype.card (Sylow p G) ≡ 1 [MOD p] := by
  sorry
  done

-- p divides the number of Sylow p subgroups -1 (where in notes???) "Alternative Sylow thm4)
theorem card_sylow_modEq_one_new [Fintype (Sylow p G)] : p ∣ Fintype.card (Sylow p G) -1 := by
  sorry
  done
=======
end Sylow_Theorems

section Sylow_Consequences

-- ==========================================
-- ===== CONSEQUENCES OF SYLOWS THEOREMS ====
-- ==========================================

variable (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [Fintype G]

-- These proofs were not possible as our issues with finiteness and type classes had meant that trying to use our theorems above would not do what we expected and occasionally we ran into errors.

-- Corollary 3.7(i) page 40 failed to state as lacked conjugation definition
theorem sylow_card_eq_index_normaliser (hdvd : p ∣ Fintype.card G) (P : Sylow p G) [Fintype (Sylow p G)] : Fintype.card (Sylow p G) = Subgroup.index (Conjugate g P) := by
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
theorem sylow_card_divides_group_order_div_sylow_order_five (hdvd: 5 ∣ Fintype.card G) (hG: Fintype.card G =20) [Fintype (Sylow 5 G)] (P : Sylow 5 G) (hP: Fintype P ): Fintype.card (Sylow 5 G) ∣ (Fintype.card G / 5) := by
  sorry
  done


example (hG : Fintype.card G = 20) [Fintype (Sylow 5 G)] (P: Subgroup G)  [Fintype P]: ¬ IsSimpleGroup G := by
  have h₀ : Nat.Prime 5 := by norm_num
  have h₁ : Fintype.card G = 2^2 * 5 :=  by linarith [hG]
  have h₂ : 5 ∣ (Fintype.card G) := by use 4
  obtain ⟨P, hP⟩ : Sylow 5 P:= by exact sylow_p_subgroup_exists_1 5 G h₂ P
  have h_3 : Fintype.card (Sylow 5 P) = 5 := by sorry
  have h₂ : Fintype.card (Sylow 5 G) ≡ 1 [MOD 5] := by sorry
  have h_6 : Fintype.card (Sylow 5 G) ∣ (Fintype.card G / Fintype.card P) := by sorry

  end Sylow_Game
