import Mathlib.GroupTheory.Sylow

-- p is a prime, G is a finite group
variable (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [Fintype G] -- decided to define variable first so we don't have to


example (hG : Fintype.card G = 20) : ¬ IsSimpleGroup G := by
  have h₀ : Nat.Prime 5 := by norm_num
  have h₁ : Fintype.card G = 2^2 * 5^1 :=  by linarith [hG]
  have h₂ : 5 ∣ (Fintype.card G) := by use 4
