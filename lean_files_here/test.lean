import Mathlib.Tactic

theorem sylow_normalizer_normal_subgroup {G : Type*} [Group G] {p : ℕ} [Fact p.Prime] (P : Sylow p G) (hN : Normalizer G P = P) : P.Normal :=
  sorry
  done
