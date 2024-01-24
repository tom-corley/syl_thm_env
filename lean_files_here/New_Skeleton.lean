-- ====================
-- ===== Imports ====== * Change as needed *
-- ====================

import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.SetLike.Fintype
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.NoncommPiCoprod
import Mathlib.Order.Atoms.Finite

-- ========================
-- ===== Definitions ======
-- ========================

open Fintype
open scoped Classical

variable {G : Type*} [Group G] [Fintype G] (p : ℕ) [Fact (Nat.Prime p)]

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


-- =====================================
-- === Necessary preliminary results ===
-- =====================================

-- content here

-- ===================================
-- ====== Sylow's Theorems 1-4 =======
-- ===================================

-- content here

-- =========================
-- ====== SYLOW GAME =======
-- =========================
