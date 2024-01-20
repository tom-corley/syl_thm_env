/-
GENERAL COMMENTS:
please change the names for definitions and theorems if you have a good idea
please add nice comments explaining our working if you have a good idea
-/

-- ====================
-- ===== Imports ======
-- ====================

-- import Mathlib.Data.ZMod.Basic --includes definition of modular equality; for example used in Sylow_4 theorem
-- import Mathlib.GroupTheory.Index -- includes definition of sylow_card_eq_index_normalizer
import Mathlib.Data.Finset.Card -- used for Sylow Thm about existence p | |G|
import Mathlib.GroupTheory.OrderOfElement -- includes orderOf used for p_subgroup_3
import Mathlib.Data.Nat.Choose.Basic -- contains Nat.choose
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Data.Nat.Choose.Dvd --lemma 3.3
import Mathlib.GroupTheory.Subgroup.Simple -- def of simple group
import Std.Data.Nat.Lemmas

-- ======================
-- === Basic examples ===
-- ======================

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

def p_subgroup: Prop := -- Original definition from Sylow.lean (Mathlib)
  ∀ g : G, ∃ k : ℕ, g ^ p ^ k = 1

def p_subgroup_2 : Prop :=   -- somehow this definition doesn't work when we tried using it in Sylow structure
 ∃ n : ℕ, Fintype.card G = p ^ n
 -- G is a finite type of cardinality p^n

def p_subgroup_3 : Prop := -- the best option we found, for all elements in G, there exists n, such that the order is p^n
  ∀ g : G, ∃ n : ℕ, orderOf g = p^n


-- Typecheck
#check p_subgroup_3

-- ** Defining a Sylow p-group, a p-group where the power of p is maximal
/-- A Sylow `p`-subgroup is a maximal `p`-subgroup. -/

-- Note that here, Subgroup G is not a single subgroup of G, but in fact the set of subgroups of G?
structure Sylow extends Subgroup G where
  p_subgroup_3' : p_subgroup_3 p toSubgroup
  -- For all subgroups of G, ???
  is_maximal' : ∀ {Q : Subgroup G}, p_subgroup_3 p Q → toSubgroup ≤ Q → Q = toSubgroup

-- Coersion?
instance : CoeOut (Sylow p G) (Subgroup G) :=
  ⟨Sylow.toSubgroup⟩

-- =====================================
-- === Necessary preliminary results ===
-- =====================================

-- proof sketch: Prove that the set Syl_p(G) of Sylow p-subgroups of a finite group G, is finite
theorem Sylow_set_finite [Fintype G] : Fintype (Sylow p G) := by
  apply?
  done

-- Defining the property that a subgroup is a Sylow-p subgroup
def issylow (K : Subgroup G) : Prop := -- this one didn't work in the Sylow Thm about existence
∀ k : K, ∃ n : ℕ, orderOf k = p ^ n ∧ ∀ (Q : Subgroup G), p_subgroup_3 p Q → K ≤ Q → Q = K

-- Define the conjugate subgroup of H by g



-- if p prime divides order of G then G has at least one Sylow p-subgroup
theorem existence_one (hdvd : p ∣ Fintype.card G) (Q : Subgroup G) : Q=Sylow p G:= by
sorry
done

-- section Sylow_1_Necessary_Lemmas_Wielandt

-- Lemma 3.3 page 36 Intro to Group Theory i)
lemma binomial_coefseff_prop1 {n m : ℕ} (hp : Nat.gcd m p = 1) : Nat.choose (m * p ^ n) (p ^ n) ≡ m [MOD p] := by
  sorry
  done

-- typecheck
#check binomial_coefseff_prop1

-- Lemma 3.3 page 36 Intro to Group Theory ii)
lemma binomial_coefsadf_prop2 (i : ℕ) (hp : p.Prime) (h : 1 ≤ i ∧ i < p) : p ∣ Nat.choose p i := by
  apply Nat.Prime.dvd_choose hp
  apply h.right
  sorry
  sorry
  --apply le_refl
  done

lemma binomial_coefsadf_prop24 (i : ℕ) (hp : p.Prime) (h : 1 ≤ i ∧ i < p) : p ∣ Nat.choose p i := by
  sorry
  --linarith
  done

-- typecheck
#check binomial_coefsadf_prop2


-- === Attempts at Conjugation for Sylow thms 2 & 3 ===
-- *************************

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

-- ===================================
-- ====== Sylow's Theorems 1-4 =======
-- ===================================

-- Sylows 1st Theorem: (Existence of a Sylow p-subgroup in G)
-- if p prime divides order of G then G has at least one Sylow p-subgroup
theorem Sylow_1 (hdvd : p ∣ Fintype.card G) (Q: Subgroup G) : Sylow p Q := by
-- hypotheses: p divides order of G, Q is a subgroup in G?
  sorry
  done

#check card_sylow_modEq_one

class subgroup [Group G] (S : Set G) : Prop :=
(mul_mem : ∀ {a b : G}, a ∈ S → b ∈ S → a * b ∈ S)
(one_mem : (1 : G) ∈ S)
(inv_mem : ∀ {a}, a ∈ S → a⁻¹ ∈ S)

-- can u see know
















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

-- ==========================================
-- ===== CONSEQUENCES OF SYLOWS THEOREMS ====
-- ==========================================

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

-- =========================
-- ====== SYLOW GAME =======
-- =========================

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
