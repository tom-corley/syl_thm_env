/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Thomas Browning
-/
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.SetLike.Fintype
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.NoncommPiCoprod
import Mathlib.Order.Atoms.Finite

#align_import group_theory.sylow from "leanprover-community/mathlib"@"4be589053caf347b899a494da75410deb55fb3ef"

/-!
# Sylow theorems

The Sylow theorems are the following results for every finite group `G` and every prime number `p`.

* There exists a Sylow `p`-subgroup of `G`.
* All Sylow `p`-subgroups of `G` are conjugate to each other.
* Let `nₚ` be the number of Sylow `p`-subgroups of `G`, then `nₚ` divides the index of the Sylow
  `p`-subgroup, `nₚ ≡ 1 [MOD p]`, and `nₚ` is equal to the index of the normalizer of the Sylow
  `p`-subgroup in `G`.

## Main definitions

* `Sylow p G` : The type of Sylow `p`-subgroups of `G`.

## Main statements

* `exists_subgroup_card_pow_prime`: A generalization of Sylow's first theorem:
  For every prime power `pⁿ` dividing the cardinality of `G`,
  there exists a subgroup of `G` of order `pⁿ`.
* `IsPGroup.exists_le_sylow`: A generalization of Sylow's first theorem:
  Every `p`-subgroup is contained in a Sylow `p`-subgroup.
* `Sylow.card_eq_multiplicity`: The cardinality of a Sylow subgroup is `p ^ n`
 where `n` is the multiplicity of `p` in the group order.
* `sylow_conjugate`: A generalization of Sylow's second theorem:
  If the number of Sylow `p`-subgroups is finite, then all Sylow `p`-subgroups are conjugate.
* `card_sylow_modEq_one`: A generalization of Sylow's third theorem:
  If the number of Sylow `p`-subgroups is finite, then it is congruent to `1` modulo `p`.
-/


open Fintype MulAction Subgroup
open scoped Classical

variables {G : Type*} [Group G] [Fintype G] (p : ℕ) [Fact (Nat.Prime p)]

def is_p_group (H : Subgroup G): Prop :=
  ∃ (n : ℕ), Fintype.card H = p ^ n

/-- A Sylow `p`-subgroup is a maximal `p`-subgroup. -/
structure Sylow extends Subgroup G where
  isPGroup' :  is_p_group p toSubgroup
  is_maximal' : ∀ {Q : Subgroup G},  is_p_group p Q → toSubgroup ≤ Q → Q = toSubgroup
#align sylow Sylow

attribute [coe] Sylow.toSubgroup

--Porting note: Changed to `CoeOut`
instance : CoeOut (Sylow p G) (Subgroup G) :=
  ⟨Sylow.toSubgroup⟩
