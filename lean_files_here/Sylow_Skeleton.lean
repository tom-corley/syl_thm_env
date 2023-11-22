/-
GENERAL COMMENTS:
please change the names for definitions and theorems if you have a good idea
please add nice comments explaining our working if you have a good idea
-/


import Mathlib.Data.ZMod.Basic --includes definition of modular equality
-- import Mathlib.GroupTheory.Index haven't used it yet but will when we talk about the index of a subgroup
import Mathlib.Data.Finset.Card -- used for Sylow Thm about existence p | |G|
import Mathlib.GroupTheory.OrderOfElement -- includes orderOf used for p_subgroup_3
import Mathlib.Data.Nat.Choose.Basic -- contains Nat.choose
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.GroupTheory.GroupAction.ConjAct




-- Basic examples

#eval 5 ≡ 8 [MOD 3]

example : 5 ≡ 8 [MOD 3] := by
rfl

#eval Nat.choose 5 2

example: Nat.choose 4 2 = 6 := by
rfl
done


-- First we define key terms or just import them

section Definitions

variable (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [Fintype G] -- decided to define variable first so we don't have to


/-- A finite p-group is a finite group in which every element has prime power order -/
def p_subgroup: Prop := -- this one was in the Sylow.lean
  ∀ g : G, ∃ k : ℕ, g ^ p ^ k = 1

def p_subgroup_2 : Prop :=   -- somehow this definitions doesn't work when we tried using it in Sylow structure
 ∃ n : ℕ, Fintype.card G = p ^ n

def p_subgroup_3 : Prop := -- the best option we found
∀ g : G, ∃ n : ℕ, orderOf g = p^n

 #check p_subgroup_3

/-- A Sylow `p`-subgroup is a maximal `p`-subgroup. -/
structure Sylow extends Subgroup G where
  p_subgroup_3' : p_subgroup_3 p toSubgroup
  is_maximal' : ∀ {Q : Subgroup G}, p_subgroup_3 p Q → toSubgroup ≤ Q → Q = toSubgroup

#check Sylow p G

def issylow (K : Subgroup G) : Prop := -- this one didn't work in the Sylow Thm about existence
∀ k : K, ∃ n : ℕ, orderOf k = p ^ n ∧ ∀ (Q : Subgroup G), p_subgroup_3 p Q → K ≤ Q → Q = K

-- Define the conjugate subgroup of H by g



-- if p prime divides order of G then G has at least one Sylow p-subgroup
theorem existence_one (hdvd : p ∣ Fintype.card G) (Q : Subgroup G) : Q=Sylow p G:= by
sorry
done

-- section Sylow_1_Necessary_Lemmas_Wielandt

-- Lemma 3.3 page 36 Intro to Group Theory i)
lemma binomial_codfseff_prop1 {n m : ℕ} (hp : Nat.gcd m p = 1) : Nat.choose (m * p ^ n) (p ^ n) ≡ m [MOD p] := by
sorry
done

#check binomial_codfseff_prop1

-- Lemma 3.3 page 36 Intro to Group Theory ii)
lemma binomial_coefsadf_prop2 (i : ℕ) (h : 1 ≤ i ∧ i < p) : p ∣ Nat.choose p i := by
sorry
done

#check binomial_coefsadf_prop2

-- section Sylow_2_3_Necessary_for_Proofs

-- def conjugadsfte (H : mysubgroup G) (g : G) : mysubgroup G :=
-- { carrier := { a : G | ∃ h ∈ H, a = g * h * g⁻¹ },
--   one_mem' := ⟨1, by simp [H.one_mem]⟩,
--   mul_mem' := by
--     rintro - - ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩,
--     refine ⟨a * b, H.mul_mem ha hb, by group⟩, -- life much easier with the `group` tactic!
--   inv_mem' := begin
--     rintro - ⟨a, ha, rfl⟩,
--     refine ⟨a⁻¹, H.inv_mem ha, by group⟩,
-- }

-- def conjugate {G : Type*} [Group G] (x : G) (H : Subgroup G) : Subgroup G where
--   carrier := {a : G | ∃ h, h ∈ H ∧ a = x * h * x⁻¹}
--   one_mem' := ⟨1, H.one_mem, by simp⟩
--   mul_mem' :=
--   begin
--     rintro - - ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩,
--     refine ⟨a * b, H.mul_mem ha hb, by group⟩, -- life much easier with the `group` tactic!
--   end,
--   inv_mem' := begin
--     rintro - ⟨a, ha, rfl⟩,
--     refine ⟨a⁻¹, H.inv_mem ha, by group⟩,
--   end }

def ConjAct212 (Q : Subgroup G) (x : G) (H : Sylow p G) : Subgroup G :=
{
  carrier := {a ∈ Q.carrier | ∃ h ∈ H.carrier, a = x * h * x⁻¹},
  one_mem' := by simp [G.one_mem],
  mul_mem' := λ ⟨a, haQ, ⟨h1, h1H, ha⟩⟩ ⟨b, hbQ, ⟨h2, h2H, hb⟩⟩ =>
    ⟨a * b, Q.mul_mem' haQ hbQ, ⟨h1 * h2, H.mul_mem' h1H h2H, by rw [←mul_assoc, ←ha, ←hb, ←mul_assoc, mul_assoc]⟩⟩,
  inv_mem' := λ ⟨a, haQ, ⟨h, hH, ha⟩⟩ =>
    ⟨a⁻¹, Q.inv_mem' haQ, ⟨h⁻¹, H.inv_mem' hH, by rw [←ha, inv_mul_eq_iff_eq_mul, mul_inv_self, mul_inv_eq_iff_eq_mul]⟩⟩
}


def ConjAct21 (Q : Subgroup G) (x : G) (H : Sylow p G) : Subgroup G :=
  { carrier := {a ∈ Q.carrier | ∃ h ∈ H.carrier, a = x * h * x⁻¹},
    one_mem' := by simp [G.one_mem],
    mul_mem' := {fun _ _ ha hb ↦
      match ha, hb with
      | ⟨a, haQ, ⟨h1, h1H, ha⟩⟩, ⟨b, hbQ, ⟨h2, h2H, hb⟩⟩ =>
        ⟨a * b, Q.mul_mem' haQ hbQ, ⟨h1 * h2, H.mul_mem' h1H h2H, by rw [←mul_assoc, ←ha, ←hb, ←mul_assoc, mul_assoc]⟩⟩},
    inv_mem' := λ _ ha ↦
      match ha with
      | ⟨a, haQ, ⟨h, hH, ha⟩⟩ =>
        ⟨a⁻¹, Q.inv_mem' haQ, ⟨h⁻¹, H.inv_mem' hH, by rw [←ha, inv_mul_eq_iff_eq_mul, mul_inv_self, mul_inv_eq_iff_eq_mul]⟩⟩

  }


def ConjAct1 (Q : Subgroup G) (x : G) (H : Sylow p G) : Subgroup G :=
  { carrier := {a ∈ Q.carrier | ∃ h ∈ H.carrier, a = x * h * x⁻¹},
    one_mem' := by simp [G.one_mem],
    mul_mem' := fun a b ha hb ↦
      ⟨a * b, Q.mul_mem' haQ hbQ, ⟨h1 * h2, H.mul_mem' h1H h2H, by rw [←mul_assoc, ←ha, ←hb, ←mul_assoc, mul_assoc]⟩⟩,
    inv_mem' := λ _ ha ↦
      ⟨a⁻¹, Q.inv_mem' haQ, ⟨h⁻¹, H.inv_mem' hH, by rw [←ha, inv_mul_eq_iff_eq_mul, mul_inv_self, mul_inv_eq_iff_eq_mul]⟩⟩
  }

def Conj2Act1 (Q : Subgroup G) (x : G) (H : Subgroup G) : Subgroup G :=
  { carrier := {a ∈ Q.carrier | ∃ h ∈ H.carrier, a = x * h * x⁻¹},
    one_mem' := by simp [G.one_mem],
    mul_mem' := λ _ _ ha hb ↦
      match ha, hb with
      | ⟨a, haQ, ⟨h1, h1H, ha⟩⟩, ⟨b, hbQ, ⟨h2, h2H, hb⟩⟩ =>
        ⟨a * b, Q.mul_mem' haQ hbQ, ⟨h1 * h2, H.mul_mem' h1H h2H, by rw [←mul_assoc, ←ha, ←hb, ←mul_assoc, mul_assoc]⟩⟩,
    inv_mem' := λ a ha ↦ by simp [(mul_assoc _ _ _).symm, ha, mul_assoc]
    }


def conjugate123 (x : G) (H : Sylow p G) : Subgroup G :=
  { carrier := {a : G | ∃ h ∈ H.carrier, a = x * h * x⁻¹},
    one_mem' := by sorry,
    mul_mem' := by sorry,
    inv_mem' := by sorry
  }

def ConjAct2312 (Q : Subgroup G) (x : G) (H : Sylow p G) : Subgroup G :=
{
  carrier := {a ∈ Q.carrier | ∃ h ∈ H.carrier, a = x * h * x⁻¹},
  one_mem' := by sorry,
  mul_mem' := by sorry,
  inv_mem' := by sorry
}
--Proposition 3.5 page 39 Intro to Group Theory I don't how to write gPg^-1 so that lean understands
theorem notsure (hdvd : p ∣ Fintype.card G) (H : Subgroup G) (P : Sylow p G): (H ⊓ (conjugate123 _ P))=Sylow p H:= by
sorry
done

#check Sylow p G

theorem card_sylow_modEq_one [Fact p.Prime] [Fintype (Sylow p G)] : Fintype.card (Sylow p G) ≡ 1 [MOD p] := by
sorry
done

#check card_sylow_modEq_one

class subgroup [Group G] (S : Set G) : Prop :=
(mul_mem : ∀ {a b : G}, a ∈ S → b ∈ S → a * b ∈ S)
(one_mem : (1 : G) ∈ S)
(inv_mem : ∀ {a}, a ∈ S → a⁻¹ ∈ S)


















-- lemma sylow_2 [fintype G] {p : ℕ} (hp : nat.prime p)
--   (H K : set G) [Sylow H hp] [Sylow K hp] :
--   ∃ g : G, H = conjugate_set g K :=
--
