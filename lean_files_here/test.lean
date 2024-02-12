import Mathlib

-- review of your code (KB)
-- (KB) for problem at the very end, it seems to be fixed by using `Finite` instead of `Fintype`.
variable (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [Finite G]

-- (KB) Your comment below should be a *docstring*, so start with `/--`, finish with `-/`
-- A group of order pq for primes p and q and such that p doesn't divide q-1, is the cyclic group of pq elements
theorem C_pq (q : ℕ) [hp : Fact p.Prime] [hq : Fact q.Prime] (hdvd: p<q ∧ Nat.card G = p*q) (h:¬(p ∣ q - 1)): IsCyclic G := by
  -- (KB) let's take a look at the statement of our theorem. We seem to have the `Fact` that p is prime
  -- twice! That might confuse the typeclass system. Look at your code. You wrote it twice,
  -- so now we have it twice.
  -- Also, why is `hdvd` two hypotheses? It could be two, `hptlq` and `hpq`.
  have h0 : p ∣ Nat.card G := by
    rw [hdvd.2]
    exact Nat.dvd_mul_right p q -- (KB) I hope you found this with `exact?`. The goal is
    -- *obviously* going to be in the library, it's such a natural statement.
  have h1 : ∃ P : Sylow p G, Nat.card P = p := by
    apply?
  sorry
