import Mathlib.Data.Nat.Prime
import Mathlib.GroupTheory.Sylow

open scoped Classical

variable (p : ℕ) [Fact p.Prime] (q : ℕ) [Fact q.Prime] (G : Type*) [Group G] [Fintype G]

theorem card_sylow_eq_one_unique_sylow [Finite (Sylow p G)] (h1: Fintype.card (Sylow p G) = 1) : Nonempty (Unique (Sylow p G)) := by
-- Fintype.card_eq_one_iff_nonempty_unique.mp h1
  exact Fintype.card_eq_one_iff_nonempty_unique.mp h1

def card_sylow_eq_one_unique_sylow_def [Finite (Sylow p G)] (h1: Fintype.card (Sylow p G) = 1) (P : Sylow p G) : Unique (Sylow p G) :=
letI := Fintype.card_le_one_iff_subsingleton.mp h1.le
uniqueOfSubsingleton P

-- If set of Sylow p-sugroups contains one element, then it is normal in G
theorem normal_of_sylow_card_eq_one [Finite (Sylow p G)] (P : Sylow p G)
(h : Fintype.card (Sylow p G) = 1) : (P : Subgroup G).Normal := by sorry
-- If G has a unique Sylow p-subgroup P, then it is normal in G  -- My goal would be to prove this theorem quickly by relying on the results above


theorem normal_of_unique [Finite (Sylow p G)] (P : Sylow p G)
(h : Nonempty (Unique (Sylow p G))) : (P : Subgroup G).Normal := by
  rw [← Fintype.card_eq_one_iff_nonempty_unique] at h
  exact normal_of_sylow_card_eq_one _ _ P h
