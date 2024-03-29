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

-- SYLOWS 1ST THEOREM (EXISTENCE)
* `exists_subgroup_card_pow_prime`: A generalization of Sylow's first theorem:
  For every prime power `pⁿ` dividing the cardinality of `G`,
  there exists a subgroup of `G` of order `pⁿ`.
* `IsPGroup.exists_le_sylow`: A generalization of Sylow's first theorem:
  Every `p`-subgroup is contained in a Sylow `p`-subgroup.

-- SIZE OF SYLOW P-SUBGROUP
* `Sylow.card_eq_multiplicity`: The cardinality of a Sylow subgroup is `p ^ n`
 where `n` is the multiplicity of `p` in the group order.


-- SYLOWS 2ND THEOREM (CONJUGACY)
* `sylow_conjugate`: A generalization of Sylow's second theorem:
  If the number of Sylow `p`-subgroups is finite, then all Sylow `p`-subgroups are conjugate.

-- SYLOW'S 4TH THEOREM (NUMBER OF SYLOW P-SUBGROUPS)
* `card_sylow_modEq_one`: A generalization of Sylow's third theorem:
  If the number of Sylow `p`-subgroups is finite, then it is congruent to `1` modulo `p`.
-/

-- This line opens namespaces in mathlib related to finite types, the multiplicative action, and subgroups
open Fintype MulAction Subgroup

-- This section does not assume groups are finite, introduces local context
section InfiniteSylow

/- Declares two variables:
  A natural number p
  G is a type variable of the most general type possible (contained within an arbitrary type universe),
  but with the added constraint that G must have a group structure -/
variable (p : ℕ) (G : Type*) [Group G]

/-- A Sylow `p`-subgroup is a maximal `p`-subgroup.
This is a type definition, defining a new structure Sylow, which extends subgroup, in this structure two axioms must be satisfied
  1) The subgroup we are extending to a Sylow subgroup, must be a p-subgroup
  2) It is a maximal p-subgroup, mathematically this is written as:
      For all Subgroups Q of G, If Q is a p-subgroup of G such that the subgroup we are defining is contained in Q, then Q is the subgroup itself.
-/
structure Sylow extends Subgroup G where
  isPGroup' : IsPGroup p toSubgroup
  is_maximal' : ∀ {Q : Subgroup G}, IsPGroup p Q → toSubgroup ≤ Q → Q = toSubgroup
#align sylow Sylow

-- Resets scope of variable p and G, making them implicit
variable {p} {G}

-- New namespace
namespace Sylow

-- This line adds a coercion attribute to Sylow.toSubgroup, coercion allows us to convert types automatically,
-- in this context, allowing us to treat a "Sylow" object like a "Subgroup"
attribute [coe] Sylow.toSubgroup

--Porting note: Changed to `CoeOut`
/- CoeOut is a typeclass used for explicit type conversion, which is very useful in lean when dealing with complex hierachical mathematical objects like groups.
  Here we are defining an instance for coercing a Sylow structure into a subgroup one, the angled brackets indicate the function Sylow.toSubgroup is used.
-/
instance : CoeOut (Sylow p G) (Subgroup G) :=
  ⟨Sylow.toSubgroup⟩

-- Porting note: syntactic tautology
-- @[simp]
-- theorem toSubgroup_eq_coe {P : Sylow p G} : P.toSubgroup = ↑P :=
--   rfl
-- Custom directive
#noalign sylow.to_subgroup_eq_coe

/- The ext atribute is used for extensionality theorems, in this case, we are proving that if two subgroups are the same,
Then they are equal in the newly defined Sylow structure. -/
@[ext]
theorem ext {P Q : Sylow p G} (h : (P : Subgroup G) = Q) : P = Q := by cases P; cases Q; congr
#align sylow.ext Sylow.ext

/- This theorem then proves the converse, extending the theorem to an if and only if statement-/
theorem ext_iff {P Q : Sylow p G} : P = Q ↔ (P : Subgroup G) = Q :=
  ⟨congr_arg _, ext⟩
#align sylow.ext_iff Sylow.ext_iff

/- Defines Sylow as an instance of the SetLike typeclass, we define the two properties needed for this typeclass:
  1) coe := we use the general coercion operator, the up arrow ↑ to define the coercion function
  2) we prove injectivty for this coercion function, that is, if two Sylow p-subgroups (the arguments _ _) have been coerced to the same object (which is the hypothesis h),
    they are indeed the same Sylow p-subgroup, we prove this by extending this injectivity from G itself  -/
instance : SetLike (Sylow p G) G where
  coe := (↑)
  coe_injective' _ _ h := ext (SetLike.coe_injective h)

/- Defines Sylow as an instance of the SubgroupClass of G, we show three properties hold,
proofs for all three use that Sylow extends Subgroup, for which these properties are already proven
  1) mul_mem, this is that the multiplicative operation is closed within Sylow p G
  2) one_mem, this is the prescence of the identiy in the subgroup
  3) inv_mem, this is the prescence of inverses for every element in the subgroup-/
instance : SubgroupClass (Sylow p G) G where
  mul_mem := Subgroup.mul_mem _
  one_mem _ := Subgroup.one_mem _
  inv_mem := Subgroup.inv_mem _

-- We now fix a Sylow p-subgroup P as a variable
variable (P : Sylow p G)

/-- The action by a Sylow subgroup is the action by the underlying group. -/
/- This instance is defined for an arbitrary type alpha, and a multiplicative left action of G on it,
  P, the Sylow p-subgroup, also acts on it by left multiplication. It has previously been proven,
  that subgroups can act on sets, so we use that P is itself a subgroup, and define this to be the action of P on α -/
instance mulActionLeft {α : Type*} [MulAction G α] : MulAction P α :=
  inferInstanceAs (MulAction (P : Subgroup G) α)
#align sylow.mul_action_left Sylow.mulActionLeft

-- K is an arbitary type with a group structure, phi is a group homomorphism to G, and N is a subgroup of G
variable {K : Type*} [Group K] (ϕ : K →* G) {N : Subgroup G}

/-- The preimage of a Sylow subgroup under a p-group-kernel homomorphism is a Sylow subgroup. -/
/- The following defines a function which takes a homomomorphism with a p group kernel, and constructs a Sylow p-Subgroup of K.
  A few clarifications: hphi is the hypothesis that the kernel of the map phi is a p-group,
  h is the hypothesis that P (coerced with ↑ from a Sylow p group to a subgroup) is a subgroup of the image of phi.

  We take the preimage (comap) of P.1 (P as a subgroup) under phi, and then prove that this is a Sylow p-Subgroup of K.

  First we show it is a p-group, this is done by using the hypothesis hphi
  Second, we show it is a maximal p-group, this is more difficult,
  we need to show an arbitrary p-subgroup Q such that P.1.comap phi is contained in Q, Q=P.1.comap phi, with some clever rewrites,
  using properties of P and the map itself, and then exact, we can finish the proof.
  -/
def comapOfKerIsPGroup (hϕ : IsPGroup p ϕ.ker) (h : ↑P ≤ ϕ.range) : Sylow p K :=
  { P.1.comap ϕ with
    isPGroup' := P.2.comap_of_ker_isPGroup ϕ hϕ
    is_maximal' := fun {Q} hQ hle => by
      show Q = P.1.comap ϕ
      rw [← P.3 (hQ.map ϕ) (le_trans (ge_of_eq (map_comap_eq_self h)) (map_mono hle))]
      exact (comap_map_eq_self ((P.1.ker_le_comap ϕ).trans hle)).symm }
#align sylow.comap_of_ker_is_p_group Sylow.comapOfKerIsPGroup

/- The following theorem proves that a coercion to a subgroup of the Sylow p-subgroup obtained in the above definition,
is the same as the pre-image obtained under phi. The proof uses the previous theorem and the coercion operator ↑-/
@[simp]
theorem coe_comapOfKerIsPGroup (hϕ : IsPGroup p ϕ.ker) (h : ↑P ≤ ϕ.range) :
    (P.comapOfKerIsPGroup ϕ hϕ h : Subgroup K) = Subgroup.comap ϕ ↑P :=
  rfl
#align sylow.coe_comap_of_ker_is_p_group Sylow.coe_comapOfKerIsPGroup

/-- The preimage of a Sylow subgroup under an injective homomorphism is a Sylow subgroup. -/
/- This definition is a special case of the more general definition of the kernel being a p group,
if the group homomorphism is injective, the kernel is trivial, and therefore a p-group.-/
def comapOfInjective (hϕ : Function.Injective ϕ) (h : ↑P ≤ ϕ.range) : Sylow p K :=
  P.comapOfKerIsPGroup ϕ (IsPGroup.ker_isPGroup_of_injective hϕ) h
#align sylow.comap_of_injective Sylow.comapOfInjective

/- The following theorem show equality between:
  The subgroup coerced from the Sylow p group we obtain from the above definition, and
  The preimage of P (coerced to a Subgroup) under phi-/
@[simp]
theorem coe_comapOfInjective (hϕ : Function.Injective ϕ) (h : ↑P ≤ ϕ.range) :
    ↑(P.comapOfInjective ϕ hϕ h) = Subgroup.comap ϕ ↑P :=
  rfl
#align sylow.coe_comap_of_injective Sylow.coe_comapOfInjective

/-- A sylow subgroup of G is also a sylow subgroup of a subgroup of G. -/
/- This definition allows us to construct a Sylow p subgroup of N, if P (coerced to a subgroup) is a subgroup of N,
the proof uses functions from earlier mathlib files and uses the inclusion map from subtype. -/
protected def subtype (h : ↑P ≤ N) : Sylow p N :=
  P.comapOfInjective N.subtype Subtype.coe_injective (by rwa [subtype_range])
#align sylow.subtype Sylow.subtype

/- This theorem states that the subgroup coerced out of the above definition is the same as the subgroupOf function,
its proven by definitional equality using the rfl tactic-/
@[simp]
theorem coe_subtype (h : ↑P ≤ N) : ↑(P.subtype h) = subgroupOf (↑P) N :=
  rfl
#align sylow.coe_subtype Sylow.coe_subtype

/- This theorem states that the subtype function we defined earlier is injective, that is, given two Sylow p-Subgroups P and Q,
 both subgroups of N, that evaluate to the same subtype group, P=Q, to prove this we use extensionality and the exact tactic.-/
theorem subtype_injective {P Q : Sylow p G} {hP : ↑P ≤ N} {hQ : ↑Q ≤ N}
    (h : P.subtype hP = Q.subtype hQ) : P = Q := by
  rw [SetLike.ext_iff] at h ⊢
  exact fun g => ⟨fun hg => (h ⟨g, hP hg⟩).mp hg, fun hg => (h ⟨g, hQ hg⟩).mpr hg⟩
#align sylow.subtype_injective Sylow.subtype_injective

-- End of the Sylow namespace
end Sylow


/-- A generalization of **Sylow's first theorem**.
  Every `p`-subgroup is contained in a Sylow `p`-subgroup. -/
-- PROOF OF SYLOWS 1st THEOREM, that is if we have a p subgroup of G, there exists a Sylow p-subgroup Q containing it.
/- Breaking down proof step by step:
  Exists.elim gets rid of the there exists quantifier, modifies goal to finding a maximal p-group x which contains P,
  We then use Zorn's Lemma from set theory to construct this maximal element in the set of Subgroups of G which are p groups
  We then need to show this element satisfies the subgroup structure, so we use some clever tactics to prove this
  the goal is altered slightly with refine' Exists.imp. The tactic rwa is used for rewrites, this proof is quite complex,
  it utilises the implementation of set theory in lean, and for full understanding, a lot of set-theoretic knowledge is necessary
  -/

theorem IsPGroup.exists_le_sylow {P : Subgroup G} (hP : IsPGroup p P) : ∃ Q : Sylow p G, P ≤ Q :=
  Exists.elim
    (zorn_nonempty_partialOrder₀ { Q : Subgroup G | IsPGroup p Q }
      (fun c hc1 hc2 Q hQ =>
        ⟨{  carrier := ⋃ R : c, R
            one_mem' := ⟨Q, ⟨⟨Q, hQ⟩, rfl⟩, Q.one_mem⟩
            inv_mem' := fun {g} ⟨_, ⟨R, rfl⟩, hg⟩ => ⟨R, ⟨R, rfl⟩, R.1.inv_mem hg⟩
            mul_mem' := fun {g} h ⟨_, ⟨R, rfl⟩, hg⟩ ⟨_, ⟨S, rfl⟩, hh⟩ =>
              (hc2.total R.2 S.2).elim (fun T => ⟨S, ⟨S, rfl⟩, S.1.mul_mem (T hg) hh⟩) fun T =>
                ⟨R, ⟨R, rfl⟩, R.1.mul_mem hg (T hh)⟩ },
          fun ⟨g, _, ⟨S, rfl⟩, hg⟩ => by
          refine' Exists.imp (fun k hk => _) (hc1 S.2 ⟨g, hg⟩)
          rwa [Subtype.ext_iff, coe_pow] at hk ⊢, fun M hM g hg => ⟨M, ⟨⟨M, hM⟩, rfl⟩, hg⟩⟩)
      P hP)
    fun {Q} ⟨hQ1, hQ2, hQ3⟩ => ⟨⟨Q, hQ1, hQ3 _⟩, hQ2⟩
#align is_p_group.exists_le_sylow IsPGroup.exists_le_sylow

/- Defines the Sylow structure as an instance of the nonempty subclass, a proof for this is simply to use the above theorem -/
instance Sylow.nonempty : Nonempty (Sylow p G) :=
  nonempty_of_exists IsPGroup.of_bot.exists_le_sylow
#align sylow.nonempty Sylow.nonempty

noncomputable instance Sylow.inhabited : Inhabited (Sylow p G) :=
  Classical.inhabited_of_nonempty Sylow.nonempty
#align sylow.inhabited Sylow.inhabited

/- This theorem states that if P is a Sylow p-Subgroup of H, and f is a Group Homomorphism from H to G,
   and the kernel of the homomorphism is a p-group, then there exists a Sylow p subgroup of G called Q,
   such that P is the pre-image Q under the group homomorphism f, the tactics used are similair to earlier comap proofs. -/
theorem Sylow.exists_comap_eq_of_ker_isPGroup {H : Type*} [Group H] (P : Sylow p H) {f : H →* G}
    (hf : IsPGroup p f.ker) : ∃ Q : Sylow p G, (Q : Subgroup G).comap f = P :=
  Exists.imp (fun Q hQ => P.3 (Q.2.comap_of_ker_isPGroup f hf) (map_le_iff_le_comap.mp hQ))
    (P.2.map f).exists_le_sylow
#align sylow.exists_comap_eq_of_ker_is_p_group Sylow.exists_comap_eq_of_ker_isPGroup

/- This theorem states that the same as above holds, if instead of assuming p-group kernel, we instead assume the injectivity of f,
   (which is equivalent to the group homomorphism having trival kernel, which is a p group for any p).-/
theorem Sylow.exists_comap_eq_of_injective {H : Type*} [Group H] (P : Sylow p H) {f : H →* G}
    (hf : Function.Injective f) : ∃ Q : Sylow p G, (Q : Subgroup G).comap f = P :=
  P.exists_comap_eq_of_ker_isPGroup (IsPGroup.ker_isPGroup_of_injective hf)
#align sylow.exists_comap_eq_of_injective Sylow.exists_comap_eq_of_injective

theorem Sylow.exists_comap_subtype_eq {H : Subgroup G} (P : Sylow p H) :
    ∃ Q : Sylow p G, (Q : Subgroup G).comap H.subtype = P :=
  P.exists_comap_eq_of_injective Subtype.coe_injective
#align sylow.exists_comap_subtype_eq Sylow.exists_comap_subtype_eq

/-- If the kernel of `f : H →* G` is a `p`-group,
  then `Fintype (Sylow p G)` implies `Fintype (Sylow p H)`. -/
/- Fintype is a typeclass in Mathlib4 used for types that contain a finite number of objects, e.g finite groups.
   This definition shows that if we have a group homomorphism from H to G, with p group kernel,
   and G has a finite number of Sylow p-Subgroups, then so does H-/
noncomputable def Sylow.fintypeOfKerIsPGroup {H : Type*} [Group H] {f : H →* G}
    (hf : IsPGroup p f.ker) [Fintype (Sylow p G)] : Fintype (Sylow p H) :=
  let h_exists := fun P : Sylow p H => P.exists_comap_eq_of_ker_isPGroup hf
  let g : Sylow p H → Sylow p G := fun P => Classical.choose (h_exists P)
  have hg : ∀ P : Sylow p H, (g P).1.comap f = P := fun P => Classical.choose_spec (h_exists P)
  Fintype.ofInjective g fun P Q h => Sylow.ext (by rw [← hg, h]; exact (h_exists Q).choose_spec)
#align sylow.fintype_of_ker_is_p_group Sylow.fintypeOfKerIsPGroup

/-- If `f : H →* G` is injective, then `Fintype (Sylow p G)` implies `Fintype (Sylow p H)`. -/
/- This is the same definition as above, but we switch the assumption from p group kernel to injectivity.-/
noncomputable def Sylow.fintypeOfInjective {H : Type*} [Group H] {f : H →* G}
    (hf : Function.Injective f) [Fintype (Sylow p G)] : Fintype (Sylow p H) :=
  Sylow.fintypeOfKerIsPGroup (IsPGroup.ker_isPGroup_of_injective hf)
#align sylow.fintype_of_injective Sylow.fintypeOfInjective

/-- If `H` is a subgroup of `G`, then `Fintype (Sylow p G)` implies `Fintype (Sylow p H)`. -/
/- This defines Sylow p H as an instance of Fintype, given that H ≤ G and G has a finite number of Sylow p-subgroups,
in other words, H also has a finite number of Sylow p-subgroups-/
noncomputable instance (H : Subgroup G) [Fintype (Sylow p G)] : Fintype (Sylow p H) :=
  Sylow.fintypeOfInjective H.subtype_injective

/-- If `H` is a subgroup of `G`, then `Finite (Sylow p G)` implies `Finite (Sylow p H)`. -/
/- The same as above but this time computable-/
instance (H : Subgroup G) [Finite (Sylow p G)] : Finite (Sylow p H) := by
  cases nonempty_fintype (Sylow p G)
  infer_instance

-- Opening new namespace / section
open Pointwise

/-- `Subgroup.pointwiseMulAction` preserves Sylow subgroups. -/
/- This shows that the pointwise multilication action of an arbitrary set alpa on G is an action,
   by verifying the Mathlib definition of Multiplicative action-/
instance Sylow.pointwiseMulAction {α : Type*} [Group α] [MulDistribMulAction α G] :
    MulAction α (Sylow p G) where
  smul g P :=
    ⟨(g • P.toSubgroup : Subgroup G), P.2.map _, fun {Q} hQ hS =>
      inv_smul_eq_iff.mp
        (P.3 (hQ.map _) fun s hs =>
          (congr_arg (· ∈ g⁻¹ • Q) (inv_smul_smul g s)).mp
            (smul_mem_pointwise_smul (g • s) g⁻¹ Q (hS (smul_mem_pointwise_smul s g P hs))))⟩
  one_smul P := Sylow.ext (one_smul α P.toSubgroup)
  mul_smul g h P := Sylow.ext (mul_smul g h P.toSubgroup)
#align sylow.pointwise_mul_action Sylow.pointwiseMulAction

/- This theorem allows us to work with cosets of Sylow p-subgroups, by writing them as subgroups, proof is by reflexivity.-/
theorem Sylow.pointwise_smul_def {α : Type*} [Group α] [MulDistribMulAction α G] {g : α}
    {P : Sylow p G} : ↑(g • P) = g • (P : Subgroup G) :=
  rfl
#align sylow.pointwise_smul_def Sylow.pointwise_smul_def

/- Defining the Action of G on the set of Sylow p-subgroups of G, by showing it is an instance of MulAction G. -/
instance Sylow.mulAction : MulAction G (Sylow p G) :=
  compHom _ MulAut.conj
#align sylow.mul_action Sylow.mulAction

/- This theorem formally states that the action of a group element on a Sylow p-subgroup via conjugation,
 is the same as applying the conjugation automorphism by that element.-/
theorem Sylow.smul_def {g : G} {P : Sylow p G} : g • P = MulAut.conj g • P :=
  rfl
#align sylow.smul_def Sylow.smul_def

/- This theorem states that conjugating P by g is the same as conjugating P as a subgroup by g.-/
theorem Sylow.coe_subgroup_smul {g : G} {P : Sylow p G} :
    ↑(g • P) = MulAut.conj g • (P : Subgroup G) :=
  rfl
#align sylow.coe_subgroup_smul Sylow.coe_subgroup_smul

/- Similair to the above proposition but we conjugate P as a set not a subgroup. -/
theorem Sylow.coe_smul {g : G} {P : Sylow p G} : ↑(g • P) = MulAut.conj g • (P : Set G) :=
  rfl
#align sylow.coe_smul Sylow.coe_smul

/- If P is a subgroup of H, its P under conjugation by some element in H is also a subgroup of H-/
theorem Sylow.smul_le {P : Sylow p G} {H : Subgroup G} (hP : ↑P ≤ H) (h : H) : ↑(h • P) ≤ H :=
  Subgroup.conj_smul_le_of_le hP h
#align sylow.smul_le Sylow.smul_le

/- This theorem is about subtypes, which I am finding difficult to pin down exactly. -/
theorem Sylow.smul_subtype {P : Sylow p G} {H : Subgroup G} (hP : ↑P ≤ H) (h : H) :
    h • P.subtype hP = (h • P).subtype (Sylow.smul_le hP h) :=
  Sylow.ext (Subgroup.conj_smul_subgroupOf hP h)
#align sylow.smul_subtype Sylow.smul_subtype

/- g is in the normaliser, of P if and only if gPg^-1 = P, basically the definition of the normaliser.
Proof uses rewrites and exact-/
theorem Sylow.smul_eq_iff_mem_normalizer {g : G} {P : Sylow p G} :
    g • P = P ↔ g ∈ (P : Subgroup G).normalizer := by
  rw [eq_comm, SetLike.ext_iff, ← inv_mem_iff (G := G) (H := normalizer P.toSubgroup),
      mem_normalizer_iff, inv_inv]
  exact
    forall_congr' fun h =>
      iff_congr Iff.rfl
        ⟨fun ⟨a, b, c⟩ => c ▸ by simpa [mul_assoc] using b,
          fun hh => ⟨(MulAut.conj g)⁻¹ h, hh, MulAut.apply_inv_self G (MulAut.conj g) h⟩⟩
#align sylow.smul_eq_iff_mem_normalizer Sylow.smul_eq_iff_mem_normalizer

/- If P is a normal Sylow p subgroup, gPg^-1 = P. Proof uses simp, follows from definition of normality.-/
theorem Sylow.smul_eq_of_normal {g : G} {P : Sylow p G} [h : (P : Subgroup G).Normal] : g • P = P :=
  by simp only [Sylow.smul_eq_iff_mem_normalizer, normalizer_eq_top.mpr h, mem_top]
#align sylow.smul_eq_of_normal Sylow.smul_eq_of_normal

/- Theorem about fixed point under conjugation, H is in the normaliser of the Sylow subgroup P,
  if and only if P is in the fixed points of the conjugation action of H on the Set of sylow p subgroups-/
theorem Subgroup.sylow_mem_fixedPoints_iff (H : Subgroup G) {P : Sylow p G} :
    P ∈ fixedPoints H (Sylow p G) ↔ H ≤ (P : Subgroup G).normalizer := by
  simp_rw [SetLike.le_def, ← Sylow.smul_eq_iff_mem_normalizer]; exact Subtype.forall
#align subgroup.sylow_mem_fixed_points_iff Subgroup.sylow_mem_fixedPoints_iff

/- Theorem states that, if P is a p-subgroup of G, and Q is a Sylow p-subgroup,
 then P intersect Q is the same as P interestect the normaliser of Q-/
theorem IsPGroup.inf_normalizer_sylow {P : Subgroup G} (hP : IsPGroup p P) (Q : Sylow p G) :
    P ⊓ (Q : Subgroup G).normalizer = P ⊓ Q :=
  le_antisymm
    (le_inf inf_le_left
      (sup_eq_right.mp
        (Q.3 (hP.to_inf_left.to_sup_of_normal_right' Q.2 inf_le_right) le_sup_right)))
    (inf_le_inf_left P le_normalizer)
#align is_p_group.inf_normalizer_sylow IsPGroup.inf_normalizer_sylow

/- This theorem states that if P is a p-subgroup of G and Q is a Sylow p subgroup of G, then
   Q is in the set of fixed points of the action of P on the set of Sylow p G subgroups, if and only if P is a subgroup of Q.-/
theorem IsPGroup.sylow_mem_fixedPoints_iff {P : Subgroup G} (hP : IsPGroup p P) {Q : Sylow p G} :
    Q ∈ fixedPoints P (Sylow p G) ↔ P ≤ Q := by
  rw [P.sylow_mem_fixedPoints_iff, ← inf_eq_left, hP.inf_normalizer_sylow, inf_eq_left]
#align is_p_group.sylow_mem_fixed_points_iff IsPGroup.sylow_mem_fixedPoints_iff

/-- A generalization of **Sylow's second theorem**.
  If the number of Sylow `p`-subgroups is finite, then all Sylow `p`-subgroups are conjugate. -/
/- SYLOW'S 2ND THEOREM, Sylow p-subgroups are conjugate, given there are a finite number of them.-/
instance [hp : Fact p.Prime] [Finite (Sylow p G)] : IsPretransitive G (Sylow p G) :=
  ⟨fun P Q => by
    classical
      cases nonempty_fintype (Sylow p G)
      have H := fun {R : Sylow p G} {S : orbit G P} =>
        calc
          S ∈ fixedPoints R (orbit G P) ↔ S.1 ∈ fixedPoints R (Sylow p G) :=
            forall_congr' fun a => Subtype.ext_iff
          _ ↔ R.1 ≤ S := R.2.sylow_mem_fixedPoints_iff
          _ ↔ S.1.1 = R := ⟨fun h => R.3 S.1.2 h, ge_of_eq⟩
      suffices Set.Nonempty (fixedPoints Q (orbit G P)) by
        exact Exists.elim this fun R hR => by
          rw [← Sylow.ext (H.mp hR)]
          exact R.2
      apply Q.2.nonempty_fixed_point_of_prime_not_dvd_card
      refine' fun h => hp.out.not_dvd_one (Nat.modEq_zero_iff_dvd.mp _)
      calc
        1 = card (fixedPoints P (orbit G P)) := ?_
        _ ≡ card (orbit G P) [MOD p] := (P.2.card_modEq_card_fixedPoints (orbit G P)).symm
        _ ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.mpr h
      rw [← Set.card_singleton (⟨P, mem_orbit_self P⟩ : orbit G P)]
      refine' card_congr' (congr_arg _ (Eq.symm _))
      rw [Set.eq_singleton_iff_unique_mem]
      exact ⟨H.mpr rfl, fun R h => Subtype.ext (Sylow.ext (H.mp h))⟩⟩

variable (p) (G)

/-- A generalization of **Sylow's third theorem**.
  If the number of Sylow `p`-subgroups is finite, then it is congruent to `1` modulo `p`. -/
/- SYLOW'S 4TH THEOREM, The number of sylow p subgroups is congruent to 1 mod p-/
theorem card_sylow_modEq_one [Fact p.Prime] [Fintype (Sylow p G)] :
    card (Sylow p G) ≡ 1 [MOD p] := by
  refine' Sylow.nonempty.elim fun P : Sylow p G => _
  have : fixedPoints P.1 (Sylow p G) = {P} :=
    Set.ext fun Q : Sylow p G =>
      calc
        Q ∈ fixedPoints P (Sylow p G) ↔ P.1 ≤ Q := P.2.sylow_mem_fixedPoints_iff
        _ ↔ Q.1 = P.1 := ⟨P.3 Q.2, ge_of_eq⟩
        _ ↔ Q ∈ {P} := Sylow.ext_iff.symm.trans Set.mem_singleton_iff.symm

  have fin : Fintype (fixedPoints P.1 (Sylow p G)) := by
    rw [this]
    infer_instance
  have : card (fixedPoints P.1 (Sylow p G)) = 1 := by simp [this]
  exact (P.2.card_modEq_card_fixedPoints (Sylow p G)).trans (by rw [this])
#align card_sylow_modeq_one card_sylow_modEq_one

/-- This theorem states that the number of Sylow p-subgroups of a finite group is not divisible by the prime p.-/
theorem not_dvd_card_sylow [hp : Fact p.Prime] [Fintype (Sylow p G)] : ¬p ∣ card (Sylow p G) :=
  fun h =>
  hp.1.ne_one
    (Nat.dvd_one.mp
      ((Nat.modEq_iff_dvd' zero_le_one).mp
        ((Nat.modEq_zero_iff_dvd.mpr h).symm.trans (card_sylow_modEq_one p G))))
#align not_dvd_card_sylow not_dvd_card_sylow

variable {p} {G}

/-- Defining an equivalence relation for a Sylow subgroup being isomorphic to its conjugate, the nonrec keyword indicates that the definition does not call itself
An equivalence relation for group isomorphisms which has been defined in previous Mathlib files is used, the new relation holds iff
the relation for general groups holds for P coerced from a Sylow group to a subgroup.
 -/
nonrec def Sylow.equivSMul (P : Sylow p G) (g : G) : P ≃* (g • P : Sylow p G) :=
  equivSMul (MulAut.conj g) P.toSubgroup
#align sylow.equiv_smul Sylow.equivSMul

/-- Similar definition for, two Sylow p subgroups in the same group, uses axiom of choice. -/
noncomputable def Sylow.equiv [Fact p.Prime] [Finite (Sylow p G)] (P Q : Sylow p G) : P ≃* Q := by
  rw [← Classical.choose_spec (exists_smul_eq G P Q)]
  exact P.equivSMul (Classical.choose (exists_smul_eq G P Q))
#align sylow.equiv Sylow.equiv

@[simp]
/- The orbit of the conjugation action on the set of Sylow p groups on the Sylow group P, is equivalent to the to top T.-/
theorem Sylow.orbit_eq_top [Fact p.Prime] [Finite (Sylow p G)] (P : Sylow p G) : orbit G P = ⊤ :=
  top_le_iff.mp fun Q _ => exists_smul_eq G P Q
#align sylow.orbit_eq_top Sylow.orbit_eq_top

/- Theorem states that the stabiliser of the action of G on the set of Sylow p groups by conjugation is the normaliser of the Sylow p group P.-/
theorem Sylow.stabilizer_eq_normalizer (P : Sylow p G) :
    stabilizer G P = (P : Subgroup G).normalizer := by
  ext; simp [Sylow.smul_eq_iff_mem_normalizer]
#align sylow.stabilizer_eq_normalizer Sylow.stabilizer_eq_normalizer

/- Theorem states that, if P is a sylow p-subgroup of a group with a finite amount of Sylow p groups,
 and there are two elements x,g in G such that both x and x conjugated by g are in the centraliser of P in G, then,
 there exists n in the normaliser of P in G, such that x conjugated by g is the same as x conjugated by n.

 The proof of the theorem uses several claims.

 Firstly h1 is the hypothesis that P coerced to a subgroup, is in the centraliser of the set generated by x in G.
 Secondly h1 is the hypothesis that P conjugated by g is in this centraliser aswell.

 These two claims are proven with rewrites and intro tactics. Following this refine and simp are used to close the goals.
 -/
theorem Sylow.conj_eq_normalizer_conj_of_mem_centralizer [Fact p.Prime] [Finite (Sylow p G)]
    (P : Sylow p G) (x g : G) (hx : x ∈ centralizer (P : Set G))
    (hy : g⁻¹ * x * g ∈ centralizer (P : Set G)) :
    ∃ n ∈ (P : Subgroup G).normalizer, g⁻¹ * x * g = n⁻¹ * x * n := by
  have h1 : ↑P ≤ centralizer (zpowers x : Set G) := by rwa [le_centralizer_iff, zpowers_le]
  have h2 : ↑(g • P) ≤ centralizer (zpowers x : Set G) := by
    rw [le_centralizer_iff, zpowers_le]
    rintro - ⟨z, hz, rfl⟩
    specialize hy z hz
    rwa [← mul_assoc, ← eq_mul_inv_iff_mul_eq, mul_assoc, mul_assoc, mul_assoc, ← mul_assoc,
      eq_inv_mul_iff_mul_eq, ← mul_assoc, ← mul_assoc] at hy
  obtain ⟨h, hh⟩ :=
    exists_smul_eq (centralizer (zpowers x : Set G)) ((g • P).subtype h2) (P.subtype h1)
  simp_rw [Sylow.smul_subtype, Subgroup.smul_def, smul_smul] at hh
  refine' ⟨h * g, Sylow.smul_eq_iff_mem_normalizer.mp (Sylow.subtype_injective hh), _⟩
  rw [← mul_assoc, Commute.right_comm (h.prop x (mem_zpowers x)), mul_inv_rev, inv_mul_cancel_right]
#align sylow.conj_eq_normalizer_conj_of_mem_centralizer Sylow.conj_eq_normalizer_conj_of_mem_centralizer

/- This theorem is similar but with slightly different assumptions, including that P is commutative. -/
theorem Sylow.conj_eq_normalizer_conj_of_mem [Fact p.Prime] [Finite (Sylow p G)] (P : Sylow p G)
    [_hP : (P : Subgroup G).IsCommutative] (x g : G) (hx : x ∈ P) (hy : g⁻¹ * x * g ∈ P) :
    ∃ n ∈ (P : Subgroup G).normalizer, g⁻¹ * x * g = n⁻¹ * x * n :=
  P.conj_eq_normalizer_conj_of_mem_centralizer x g (le_centralizer P hx) (le_centralizer P hy)
#align sylow.conj_eq_normalizer_conj_of_mem Sylow.conj_eq_normalizer_conj_of_mem

/-- Sylow `p`-subgroups are in bijection with cosets of the normalizer of a Sylow `p`-subgroup -/
noncomputable def Sylow.equivQuotientNormalizer [Fact p.Prime] [Fintype (Sylow p G)]
    (P : Sylow p G) : Sylow p G ≃ G ⧸ (P : Subgroup G).normalizer :=
  calc
    Sylow p G ≃ (⊤ : Set (Sylow p G)) := (Equiv.Set.univ (Sylow p G)).symm
    _ ≃ orbit G P := by rw [P.orbit_eq_top]
    _ ≃ G ⧸ stabilizer G P := (orbitEquivQuotientStabilizer G P)
    _ ≃ G ⧸ (P : Subgroup G).normalizer := by rw [P.stabilizer_eq_normalizer]

#align sylow.equiv_quotient_normalizer Sylow.equivQuotientNormalizer

/- -/
noncomputable instance [Fact p.Prime] [Fintype (Sylow p G)] (P : Sylow p G) :
    Fintype (G ⧸ (P : Subgroup G).normalizer) :=
  ofEquiv (Sylow p G) P.equivQuotientNormalizer

/- Corollary 3.7 from MA3K4 i) the number of Sylow p Subgroups is equal to the size of the quotient group of G,
with the normaliser of P in G-/
theorem card_sylow_eq_card_quotient_normalizer [Fact p.Prime] [Fintype (Sylow p G)]
    (P : Sylow p G) : card (Sylow p G) = card (G ⧸ (P : Subgroup G).normalizer) :=
  card_congr P.equivQuotientNormalizer
#align card_sylow_eq_card_quotient_normalizer card_sylow_eq_card_quotient_normalizer

/- Equivalent to above theorem but uses index instead of size of quotient group. -/
theorem card_sylow_eq_index_normalizer [Fact p.Prime] [Fintype (Sylow p G)] (P : Sylow p G) :
    card (Sylow p G) = (P : Subgroup G).normalizer.index :=
  (card_sylow_eq_card_quotient_normalizer P).trans (P : Subgroup G).normalizer.index_eq_card.symm
#align card_sylow_eq_index_normalizer card_sylow_eq_index_normalizer

/- The number of Sylow p subgroups divides the index of P in G.-/
theorem card_sylow_dvd_index [Fact p.Prime] [Fintype (Sylow p G)] (P : Sylow p G) :
    card (Sylow p G) ∣ (P : Subgroup G).index :=
  ((congr_arg _ (card_sylow_eq_index_normalizer P)).mp dvd_rfl).trans
    (index_dvd_of_le le_normalizer)
#align card_sylow_dvd_index card_sylow_dvd_index

/- The below theorem shows that if P in normal in G, then p does not divide the index of P in G. -/
theorem not_dvd_index_sylow' [hp : Fact p.Prime] (P : Sylow p G) [(P : Subgroup G).Normal]
    [fP : FiniteIndex (P : Subgroup G)] : ¬p ∣ (P : Subgroup G).index := by
  intro h
  letI : Fintype (G ⧸ (P : Subgroup G)) := (P : Subgroup G).fintypeQuotientOfFiniteIndex
  rw [index_eq_card (P : Subgroup G)] at h
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card (G := G ⧸ (P : Subgroup G)) p h
  have h := IsPGroup.of_card ((Fintype.card_zpowers.trans hx).trans (pow_one p).symm)
  let Q := (zpowers x).comap (QuotientGroup.mk' (P : Subgroup G))
  have hQ : IsPGroup p Q := by
    apply h.comap_of_ker_isPGroup
    rw [QuotientGroup.ker_mk']
    exact P.2
  replace hp := mt orderOf_eq_one_iff.mpr (ne_of_eq_of_ne hx hp.1.ne_one)
  rw [← zpowers_eq_bot, ← Ne, ← bot_lt_iff_ne_bot, ←
    comap_lt_comap_of_surjective (QuotientGroup.mk'_surjective _), MonoidHom.comap_bot,
    QuotientGroup.ker_mk'] at hp
  exact hp.ne' (P.3 hQ hp.le)
#align not_dvd_index_sylow' not_dvd_index_sylow'

/- Same as above but with slightly altered assumptions, instead assuming the normaliser of P is not zero. -/
theorem not_dvd_index_sylow [hp : Fact p.Prime] [Finite (Sylow p G)] (P : Sylow p G)
    (hP : relindex ↑P (P : Subgroup G).normalizer ≠ 0) : ¬p ∣ (P : Subgroup G).index := by
  cases nonempty_fintype (Sylow p G)
  rw [← relindex_mul_index le_normalizer, ← card_sylow_eq_index_normalizer]
  haveI : (P.subtype le_normalizer : Subgroup (P : Subgroup G).normalizer).Normal :=
    Subgroup.normal_in_normalizer
  haveI : FiniteIndex ↑(P.subtype le_normalizer : Subgroup (P : Subgroup G).normalizer) := ⟨hP⟩
  replace hP := not_dvd_index_sylow' (P.subtype le_normalizer)
  exact hp.1.not_dvd_mul hP (not_dvd_card_sylow p G)
#align not_dvd_index_sylow not_dvd_index_sylow

/-- **Frattini's Argument**: If `N` is a normal subgroup of `G`, and if `P` is a Sylow `p`-subgroup
  of `N`, then `N_G(P) ⊔ N = G`. -/
theorem Sylow.normalizer_sup_eq_top {p : ℕ} [Fact p.Prime] {N : Subgroup G} [N.Normal]
    [Finite (Sylow p N)] (P : Sylow p N) :
    ((↑P : Subgroup N).map N.subtype).normalizer ⊔ N = ⊤ := by
  refine' top_le_iff.mp fun g _ => _
  obtain ⟨n, hn⟩ := exists_smul_eq N ((MulAut.conjNormal g : MulAut N) • P) P
  rw [← inv_mul_cancel_left (↑n) g, sup_comm]
  apply mul_mem_sup (N.inv_mem n.2)
  rw [Sylow.smul_def, ← mul_smul, ← MulAut.conjNormal_val, ← MulAut.conjNormal.map_mul,
    Sylow.ext_iff, Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def] at hn
  refine' fun x =>
    (mem_map_iff_mem
            (show Function.Injective (MulAut.conj (↑n * g)).toMonoidHom from
              (MulAut.conj (↑n * g)).injective)).symm.trans
      _
  rw [map_map, ← congr_arg (map N.subtype) hn, map_map]
  rfl
#align sylow.normalizer_sup_eq_top Sylow.normalizer_sup_eq_top

/-- **Frattini's Argument**: If `N` is a normal subgroup of `G`, and if `P` is a Sylow `p`-subgroup
  of `N`, then `N_G(P) ⊔ N = G`. -/
theorem Sylow.normalizer_sup_eq_top' {p : ℕ} [Fact p.Prime] {N : Subgroup G} [N.Normal]
    [Finite (Sylow p N)] (P : Sylow p G) (hP : ↑P ≤ N) : (P : Subgroup G).normalizer ⊔ N = ⊤ := by
  rw [← Sylow.normalizer_sup_eq_top (P.subtype hP), P.coe_subtype, subgroupOf_map_subtype,
    inf_of_le_left hP]
#align sylow.normalizer_sup_eq_top' Sylow.normalizer_sup_eq_top'

end InfiniteSylow

open Equiv Equiv.Perm Finset Function List QuotientGroup

open BigOperators

universe u v w

variable {G : Type u} {α : Type v} {β : Type w} [Group G]

attribute [local instance 10] Subtype.fintype setFintype Classical.propDecidable

theorem QuotientGroup.card_preimage_mk [Fintype G] (s : Subgroup G) (t : Set (G ⧸ s)) :
    Fintype.card (QuotientGroup.mk ⁻¹' t) = Fintype.card s * Fintype.card t := by
  rw [← Fintype.card_prod, Fintype.card_congr (preimageMkEquivSubgroupProdSet _ _)]
#align quotient_group.card_preimage_mk QuotientGroup.card_preimage_mk

namespace Sylow
theorem mem_fixedPoints_mul_left_cosets_iff_mem_normalizer {H : Subgroup G} [Finite (H : Set G)]
    {x : G} : (x : G ⧸ H) ∈ MulAction.fixedPoints H (G ⧸ H) ↔ x ∈ normalizer H :=
  ⟨fun hx =>
    have ha : ∀ {y : G ⧸ H}, y ∈ orbit H (x : G ⧸ H) → y = x := mem_fixedPoints'.1 hx _
    (inv_mem_iff (G := G)).1
      (mem_normalizer_fintype fun n (hn : n ∈ H) =>
        have : (n⁻¹ * x)⁻¹ * x ∈ H := QuotientGroup.eq.1 (ha ⟨⟨n⁻¹, inv_mem hn⟩, rfl⟩)
        show _ ∈ H by
          rw [mul_inv_rev, inv_inv] at this
          convert this
          rw [inv_inv]),
    fun hx : ∀ n : G, n ∈ H ↔ x * n * x⁻¹ ∈ H =>
    mem_fixedPoints'.2 fun y =>
      Quotient.inductionOn' y fun y hy =>
        QuotientGroup.eq.2
          (let ⟨⟨b, hb₁⟩, hb₂⟩ := hy
          have hb₂ : (b * x)⁻¹ * y ∈ H := QuotientGroup.eq.1 hb₂
          (inv_mem_iff (G := G)).1 <|
            (hx _).2 <|
              (mul_mem_cancel_left (inv_mem hb₁)).1 <| by
                rw [hx] at hb₂; simpa [mul_inv_rev, mul_assoc] using hb₂)⟩
#align sylow.mem_fixed_points_mul_left_cosets_iff_mem_normalizer Sylow.mem_fixedPoints_mul_left_cosets_iff_mem_normalizer

/-- The fixed points of the action of `H` on its cosets correspond to `normalizer H / H`. -/
def fixedPointsMulLeftCosetsEquivQuotient (H : Subgroup G) [Finite (H : Set G)] :
    MulAction.fixedPoints H (G ⧸ H) ≃
      normalizer H ⧸ Subgroup.comap ((normalizer H).subtype : normalizer H →* G) H :=
  @subtypeQuotientEquivQuotientSubtype G (normalizer H : Set G) (_) (_)
    (MulAction.fixedPoints H (G ⧸ H))
    (fun a => (@mem_fixedPoints_mul_left_cosets_iff_mem_normalizer _ _ _ ‹_› _).symm)
    (by
      intros
      dsimp only [instHasEquiv]
      rw [leftRel_apply (α := normalizer H), leftRel_apply]
      rfl)
#align sylow.fixed_points_mul_left_cosets_equiv_quotient Sylow.fixedPointsMulLeftCosetsEquivQuotient

/-- If `H` is a `p`-subgroup of `G`, then the index of `H` inside its normalizer is congruent
  mod `p` to the index of `H`.  -/
theorem card_quotient_normalizer_modEq_card_quotient [Fintype G] {p : ℕ} {n : ℕ} [hp : Fact p.Prime]
    {H : Subgroup G} (hH : Fintype.card H = p ^ n) :
    Fintype.card (normalizer H ⧸ Subgroup.comap ((normalizer H).subtype : normalizer H →* G) H) ≡
      card (G ⧸ H) [MOD p] := by
  rw [← Fintype.card_congr (fixedPointsMulLeftCosetsEquivQuotient H)]
  exact ((IsPGroup.of_card hH).card_modEq_card_fixedPoints _).symm
#align sylow.card_quotient_normalizer_modeq_card_quotient Sylow.card_quotient_normalizer_modEq_card_quotient

/-- If `H` is a subgroup of `G` of cardinality `p ^ n`, then the cardinality of the
  normalizer of `H` is congruent mod `p ^ (n + 1)` to the cardinality of `G`.  -/
theorem card_normalizer_modEq_card [Fintype G] {p : ℕ} {n : ℕ} [hp : Fact p.Prime] {H : Subgroup G}
    (hH : Fintype.card H = p ^ n) : card (normalizer H) ≡ card G [MOD p ^ (n + 1)] := by
  have : H.subgroupOf (normalizer H) ≃ H := (subgroupOfEquivOfLe le_normalizer).toEquiv
  rw [card_eq_card_quotient_mul_card_subgroup H,
    card_eq_card_quotient_mul_card_subgroup (H.subgroupOf (normalizer H)), Fintype.card_congr this,
    hH, pow_succ]
  exact (card_quotient_normalizer_modEq_card_quotient hH).mul_right' _
#align sylow.card_normalizer_modeq_card Sylow.card_normalizer_modEq_card

/-- If `H` is a `p`-subgroup but not a Sylow `p`-subgroup, then `p` divides the
  index of `H` inside its normalizer. -/
theorem prime_dvd_card_quotient_normalizer [Fintype G] {p : ℕ} {n : ℕ} [hp : Fact p.Prime]
    (hdvd : p ^ (n + 1) ∣ card G) {H : Subgroup G} (hH : Fintype.card H = p ^ n) :
    p ∣ card (normalizer H ⧸ Subgroup.comap ((normalizer H).subtype : normalizer H →* G) H) :=
  let ⟨s, hs⟩ := exists_eq_mul_left_of_dvd hdvd
  have hcard : card (G ⧸ H) = s * p :=
    (mul_left_inj' (show card H ≠ 0 from Fintype.card_ne_zero)).1
      (by
        rw [← card_eq_card_quotient_mul_card_subgroup H, hH, hs, pow_succ', mul_assoc, mul_comm p])
  have hm :
    s * p % p =
      card (normalizer H ⧸ Subgroup.comap ((normalizer H).subtype : normalizer H →* G) H) % p :=
    hcard ▸ (card_quotient_normalizer_modEq_card_quotient hH).symm
  Nat.dvd_of_mod_eq_zero (by rwa [Nat.mod_eq_zero_of_dvd (dvd_mul_left _ _), eq_comm] at hm)
#align sylow.prime_dvd_card_quotient_normalizer Sylow.prime_dvd_card_quotient_normalizer

/-- If `H` is a `p`-subgroup but not a Sylow `p`-subgroup of cardinality `p ^ n`,
  then `p ^ (n + 1)` divides the cardinality of the normalizer of `H`. -/
theorem prime_pow_dvd_card_normalizer [Fintype G] {p : ℕ} {n : ℕ} [_hp : Fact p.Prime]
    (hdvd : p ^ (n + 1) ∣ card G) {H : Subgroup G} (hH : Fintype.card H = p ^ n) :
    p ^ (n + 1) ∣ card (normalizer H) :=
  Nat.modEq_zero_iff_dvd.1 ((card_normalizer_modEq_card hH).trans hdvd.modEq_zero_nat)
#align sylow.prime_pow_dvd_card_normalizer Sylow.prime_pow_dvd_card_normalizer

/-- If `H` is a subgroup of `G` of cardinality `p ^ n`,
  then `H` is contained in a subgroup of cardinality `p ^ (n + 1)`
  if `p ^ (n + 1)` divides the cardinality of `G` -/
theorem exists_subgroup_card_pow_succ [Fintype G] {p : ℕ} {n : ℕ} [hp : Fact p.Prime]
    (hdvd : p ^ (n + 1) ∣ card G) {H : Subgroup G} (hH : Fintype.card H = p ^ n) :
    ∃ K : Subgroup G, Fintype.card K = p ^ (n + 1) ∧ H ≤ K :=
  let ⟨s, hs⟩ := exists_eq_mul_left_of_dvd hdvd
  have hcard : card (G ⧸ H) = s * p :=
    (mul_left_inj' (show card H ≠ 0 from Fintype.card_ne_zero)).1
      (by
        rw [← card_eq_card_quotient_mul_card_subgroup H, hH, hs, pow_succ', mul_assoc, mul_comm p])
  have hm : s * p % p = card (normalizer H ⧸ H.subgroupOf H.normalizer) % p :=
    Fintype.card_congr (fixedPointsMulLeftCosetsEquivQuotient H) ▸
      hcard ▸ (IsPGroup.of_card hH).card_modEq_card_fixedPoints _
  have hm' : p ∣ card (normalizer H ⧸ H.subgroupOf H.normalizer) :=
    Nat.dvd_of_mod_eq_zero (by rwa [Nat.mod_eq_zero_of_dvd (dvd_mul_left _ _), eq_comm] at hm)
  let ⟨x, hx⟩ := @exists_prime_orderOf_dvd_card _ (QuotientGroup.Quotient.group _) _ _ hp hm'
  have hequiv : H ≃ H.subgroupOf H.normalizer := (subgroupOfEquivOfLe le_normalizer).symm.toEquiv
  ⟨Subgroup.map (normalizer H).subtype
      (Subgroup.comap (mk' (H.subgroupOf H.normalizer)) (zpowers x)), by
    show Fintype.card (Subgroup.map H.normalizer.subtype
              (comap (mk' (H.subgroupOf H.normalizer)) (Subgroup.zpowers x))) = p ^ (n + 1)
    suffices Fintype.card (Subtype.val ''
              (Subgroup.comap (mk' (H.subgroupOf H.normalizer)) (zpowers x) : Set H.normalizer)) =
        p ^ (n + 1)
      by convert this using 2
    rw [Set.card_image_of_injective
        (Subgroup.comap (mk' (H.subgroupOf H.normalizer)) (zpowers x) : Set H.normalizer)
        Subtype.val_injective,
      pow_succ', ← hH, Fintype.card_congr hequiv, ← hx, ← Fintype.card_zpowers, ←
      Fintype.card_prod]
    exact @Fintype.card_congr _ _ (_) (_)
      (preimageMkEquivSubgroupProdSet (H.subgroupOf H.normalizer) (zpowers x)), by
    intro y hy
    simp only [exists_prop, Subgroup.coeSubtype, mk'_apply, Subgroup.mem_map, Subgroup.mem_comap]
    refine' ⟨⟨y, le_normalizer hy⟩, ⟨0, _⟩, rfl⟩
    dsimp only
    rw [zpow_zero, eq_comm, QuotientGroup.eq_one_iff]
    simpa using hy⟩
#align sylow.exists_subgroup_card_pow_succ Sylow.exists_subgroup_card_pow_succ

/-- If `H` is a subgroup of `G` of cardinality `p ^ n`,
  then `H` is contained in a subgroup of cardinality `p ^ m`
  if `n ≤ m` and `p ^ m` divides the cardinality of `G` -/
theorem exists_subgroup_card_pow_prime_le [Fintype G] (p : ℕ) :
    ∀ {n m : ℕ} [_hp : Fact p.Prime] (_hdvd : p ^ m ∣ card G) (H : Subgroup G)
      (_hH : card H = p ^ n) (_hnm : n ≤ m), ∃ K : Subgroup G, card K = p ^ m ∧ H ≤ K
  | n, m => fun {hdvd H hH hnm} =>
    (lt_or_eq_of_le hnm).elim
      (fun hnm : n < m =>
        have h0m : 0 < m := lt_of_le_of_lt n.zero_le hnm
        have _wf : m - 1 < m := Nat.sub_lt h0m zero_lt_one
        have hnm1 : n ≤ m - 1 := le_tsub_of_add_le_right hnm
        let ⟨K, hK⟩ :=
          @exists_subgroup_card_pow_prime_le _ _ n (m - 1) _
            (Nat.pow_dvd_of_le_of_pow_dvd tsub_le_self hdvd) H hH hnm1
        have hdvd' : p ^ (m - 1 + 1) ∣ card G := by rwa [tsub_add_cancel_of_le h0m.nat_succ_le]
        let ⟨K', hK'⟩ := @exists_subgroup_card_pow_succ _ _ _ _ _ _ hdvd' K hK.1
        ⟨K', by rw [hK'.1, tsub_add_cancel_of_le h0m.nat_succ_le], le_trans hK.2 hK'.2⟩)
      fun hnm : n = m => ⟨H, by simp [hH, hnm]⟩
#align sylow.exists_subgroup_card_pow_prime_le Sylow.exists_subgroup_card_pow_prime_le

/-- A generalisation of **Sylow's first theorem**. If `p ^ n` divides
  the cardinality of `G`, then there is a subgroup of cardinality `p ^ n` -/
theorem exists_subgroup_card_pow_prime [Fintype G] (p : ℕ) {n : ℕ} [Fact p.Prime]
    (hdvd : p ^ n ∣ card G) : ∃ K : Subgroup G, Fintype.card K = p ^ n :=
  let ⟨K, hK⟩ := exists_subgroup_card_pow_prime_le p hdvd ⊥ (card_bot.trans (by simp)) n.zero_le
  ⟨K, hK.1⟩
#align sylow.exists_subgroup_card_pow_prime Sylow.exists_subgroup_card_pow_prime

/-- A special case of **Sylow's first theorem**. If `G` is a `p`-group of size at least `p ^ n`
then there is a subgroup of cardinality `p ^ n`. -/
lemma exists_subgroup_card_pow_prime_of_le_card {n p : ℕ} (hp : p.Prime) (h : IsPGroup p G)
    (hn : p ^ n ≤ Nat.card G) : ∃ H : Subgroup G, Nat.card H = p ^ n := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite G := Nat.finite_of_card_ne_zero <| by linarith [Nat.one_le_pow n p hp.pos]
  cases nonempty_fintype G
  obtain ⟨m, hm⟩ := h.exists_card_eq
  simp_rw [Nat.card_eq_fintype_card] at hm hn ⊢
  refine exists_subgroup_card_pow_prime _ ?_
  rw [hm] at hn ⊢
  exact pow_dvd_pow _ <| (pow_le_pow_iff_right hp.one_lt).1 hn

/-- A special case of **Sylow's first theorem**. If `G` is a `p`-group and `H` a subgroup of size at
least `p ^ n` then there is a subgroup of `H` of cardinality `p ^ n`. -/
lemma exists_subgroup_le_card_pow_prime_of_le_card {n p : ℕ} (hp : p.Prime) (h : IsPGroup p G)
    {H : Subgroup G} (hn : p ^ n ≤ Nat.card H) : ∃ H' ≤ H, Nat.card H' = p ^ n := by
  obtain ⟨H', H'card⟩ := exists_subgroup_card_pow_prime_of_le_card hp (h.to_subgroup H) hn
  refine ⟨H'.map H.subtype, map_subtype_le _, ?_⟩
  rw [← H'card]
  let e : H' ≃* H'.map H.subtype := H'.equivMapOfInjective (Subgroup.subtype H) H.subtype_injective
  exact Nat.card_congr e.symm.toEquiv

/-- A special case of **Sylow's first theorem**. If `G` is a `p`-group and `H` a subgroup of size at
least `k` then there is a subgroup of `H` of cardinality between `k / p` and `k`. -/
lemma exists_subgroup_le_card_le {k p : ℕ} (hp : p.Prime) (h : IsPGroup p G) {H : Subgroup G}
    (hk : k ≤ Nat.card H) (hk₀ : k ≠ 0) : ∃ H' ≤ H, Nat.card H' ≤ k ∧ k < p * Nat.card H' := by
  obtain ⟨m, hmk, hkm⟩ : ∃ s, p ^ s ≤ k ∧ k < p ^ (s + 1) :=
    exists_nat_pow_near (Nat.one_le_iff_ne_zero.2 hk₀) hp.one_lt
  obtain ⟨H', H'H, H'card⟩ := exists_subgroup_le_card_pow_prime_of_le_card hp h (hmk.trans hk)
  refine ⟨H', H'H, ?_⟩
  simpa only [pow_succ, H'card] using And.intro hmk hkm

theorem pow_dvd_card_of_pow_dvd_card [Fintype G] {p n : ℕ} [hp : Fact p.Prime] (P : Sylow p G)
    (hdvd : p ^ n ∣ card G) : p ^ n ∣ card P :=
  (hp.1.coprime_pow_of_not_dvd
          (not_dvd_index_sylow P index_ne_zero_of_finite)).symm.dvd_of_dvd_mul_left
    ((index_mul_card P.1).symm ▸ hdvd)
#align sylow.pow_dvd_card_of_pow_dvd_card Sylow.pow_dvd_card_of_pow_dvd_card

theorem dvd_card_of_dvd_card [Fintype G] {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (hdvd : p ∣ card G) : p ∣ card P := by
  rw [← pow_one p] at hdvd
  have key := P.pow_dvd_card_of_pow_dvd_card hdvd
  rwa [pow_one] at key
#align sylow.dvd_card_of_dvd_card Sylow.dvd_card_of_dvd_card

/-- Sylow subgroups are Hall subgroups. -/
theorem card_coprime_index [Fintype G] {p : ℕ} [hp : Fact p.Prime] (P : Sylow p G) :
    (card P).Coprime (index (P : Subgroup G)) :=
  let ⟨_n, hn⟩ := IsPGroup.iff_card.mp P.2
  hn.symm ▸ (hp.1.coprime_pow_of_not_dvd (not_dvd_index_sylow P index_ne_zero_of_finite)).symm
#align sylow.card_coprime_index Sylow.card_coprime_index

theorem ne_bot_of_dvd_card [Fintype G] {p : ℕ} [hp : Fact p.Prime] (P : Sylow p G)
    (hdvd : p ∣ card G) : (P : Subgroup G) ≠ ⊥ := by
  refine' fun h => hp.out.not_dvd_one _
  have key : p ∣ card (P : Subgroup G) := P.dvd_card_of_dvd_card hdvd
  rwa [h, card_bot] at key
#align sylow.ne_bot_of_dvd_card Sylow.ne_bot_of_dvd_card

/-- The cardinality of a Sylow subgroup is `p ^ n`
 where `n` is the multiplicity of `p` in the group order. -/
theorem card_eq_multiplicity [Fintype G] {p : ℕ} [hp : Fact p.Prime] (P : Sylow p G) :
    card P = p ^ Nat.factorization (card G) p := by
  obtain ⟨n, heq : card P = _⟩ := IsPGroup.iff_card.mp P.isPGroup'
  refine' Nat.dvd_antisymm _ (P.pow_dvd_card_of_pow_dvd_card (Nat.ord_proj_dvd _ p))
  rw [heq, ← hp.out.pow_dvd_iff_dvd_ord_proj (show card G ≠ 0 from card_ne_zero), ← heq]
  exact P.1.card_subgroup_dvd_card
#align sylow.card_eq_multiplicity Sylow.card_eq_multiplicity

/-- A subgroup with cardinality `p ^ n` is a Sylow subgroup
 where `n` is the multiplicity of `p` in the group order. -/
def ofCard [Fintype G] {p : ℕ} [Fact p.Prime] (H : Subgroup G) [Fintype H]
    (card_eq : card H = p ^ (card G).factorization p) : Sylow p G
    where
  toSubgroup := H
  isPGroup' := IsPGroup.of_card card_eq
  is_maximal' := by
    obtain ⟨P, hHP⟩ := (IsPGroup.of_card card_eq).exists_le_sylow
    exact SetLike.ext'
      (Set.eq_of_subset_of_card_le hHP (P.card_eq_multiplicity.trans card_eq.symm).le).symm ▸ P.3
#align sylow.of_card Sylow.ofCard

@[simp, norm_cast]
theorem coe_ofCard [Fintype G] {p : ℕ} [Fact p.Prime] (H : Subgroup G) [Fintype H]
    (card_eq : card H = p ^ (card G).factorization p) : ↑(ofCard H card_eq) = H :=
  rfl
#align sylow.coe_of_card Sylow.coe_ofCard

/-- If `G` has a normal Sylow `p`-subgroup, then it is the only Sylow `p`-subgroup. -/
noncomputable def unique_of_normal {p : ℕ} [Fact p.Prime] [Finite (Sylow p G)] (P : Sylow p G)
    (h : (P : Subgroup G).Normal) : Unique (Sylow p G) := by
  refine { uniq := fun Q ↦ ?_ }
  obtain ⟨x, h1⟩ := exists_smul_eq G P Q
  obtain ⟨x, h2⟩ := exists_smul_eq G P default
  rw [Sylow.smul_eq_of_normal] at h1 h2
  rw [← h1, ← h2]
#align sylow.subsingleton_of_normal Sylow.unique_of_normal

section Pointwise

open Pointwise

theorem characteristic_of_normal {p : ℕ} [Fact p.Prime] [Finite (Sylow p G)] (P : Sylow p G)
    (h : (P : Subgroup G).Normal) : (P : Subgroup G).Characteristic := by
  haveI := Sylow.unique_of_normal P h
  rw [characteristic_iff_map_eq]
  intro Φ
  show (Φ • P).toSubgroup = P.toSubgroup
  congr
  simp [eq_iff_true_of_subsingleton]
#align sylow.characteristic_of_normal Sylow.characteristic_of_normal

end Pointwise

theorem normal_of_normalizer_normal {p : ℕ} [Fact p.Prime] [Finite (Sylow p G)] (P : Sylow p G)
    (hn : (↑P : Subgroup G).normalizer.Normal) : (↑P : Subgroup G).Normal := by
  rw [← normalizer_eq_top, ← normalizer_sup_eq_top' P le_normalizer, sup_idem]
#align sylow.normal_of_normalizer_normal Sylow.normal_of_normalizer_normal

@[simp]
theorem normalizer_normalizer {p : ℕ} [Fact p.Prime] [Finite (Sylow p G)] (P : Sylow p G) :
    (↑P : Subgroup G).normalizer.normalizer = (↑P : Subgroup G).normalizer := by
  have := normal_of_normalizer_normal (P.subtype (le_normalizer.trans le_normalizer))
  simp_rw [← normalizer_eq_top, Sylow.coe_subtype, ← subgroupOf_normalizer_eq le_normalizer, ←
    subgroupOf_normalizer_eq le_rfl, subgroupOf_self] at this
  rw [← subtype_range (P : Subgroup G).normalizer.normalizer, MonoidHom.range_eq_map,
    ← this trivial]
  exact map_comap_eq_self (le_normalizer.trans (ge_of_eq (subtype_range _)))
#align sylow.normalizer_normalizer Sylow.normalizer_normalizer

theorem normal_of_all_max_subgroups_normal [Finite G]
    (hnc : ∀ H : Subgroup G, IsCoatom H → H.Normal) {p : ℕ} [Fact p.Prime] [Finite (Sylow p G)]
    (P : Sylow p G) : (↑P : Subgroup G).Normal :=
  normalizer_eq_top.mp
    (by
      rcases eq_top_or_exists_le_coatom (↑P : Subgroup G).normalizer with (heq | ⟨K, hK, hNK⟩)
      · exact heq
      · haveI := hnc _ hK
        have hPK : ↑P ≤ K := le_trans le_normalizer hNK
        refine' (hK.1 _).elim
        rw [← sup_of_le_right hNK, P.normalizer_sup_eq_top' hPK])
#align sylow.normal_of_all_max_subgroups_normal Sylow.normal_of_all_max_subgroups_normal

theorem normal_of_normalizerCondition (hnc : NormalizerCondition G) {p : ℕ} [Fact p.Prime]
    [Finite (Sylow p G)] (P : Sylow p G) : (↑P : Subgroup G).Normal :=
  normalizer_eq_top.mp <|
    normalizerCondition_iff_only_full_group_self_normalizing.mp hnc _ <| normalizer_normalizer _
#align sylow.normal_of_normalizer_condition Sylow.normal_of_normalizerCondition

open BigOperators

/-- If all its Sylow subgroups are normal, then a finite group is isomorphic to the direct product
of these Sylow subgroups.
-/
noncomputable def directProductOfNormal [Fintype G]
    (hn : ∀ {p : ℕ} [Fact p.Prime] (P : Sylow p G), (↑P : Subgroup G).Normal) :
    (∀ p : (card G).primeFactors, ∀ P : Sylow p G, (↑P : Subgroup G)) ≃* G := by
  set ps := (Fintype.card G).primeFactors
  -- “The” Sylow subgroup for p
  let P : ∀ p, Sylow p G := default
  have hcomm : Pairwise fun p₁ p₂ : ps => ∀ x y : G, x ∈ P p₁ → y ∈ P p₂ → Commute x y := by
    rintro ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩ hne
    haveI hp₁' := Fact.mk (Nat.prime_of_mem_primeFactors hp₁)
    haveI hp₂' := Fact.mk (Nat.prime_of_mem_primeFactors hp₂)
    have hne' : p₁ ≠ p₂ := by simpa using hne
    apply Subgroup.commute_of_normal_of_disjoint _ _ (hn (P p₁)) (hn (P p₂))
    apply IsPGroup.disjoint_of_ne p₁ p₂ hne' _ _ (P p₁).isPGroup' (P p₂).isPGroup'
  refine' MulEquiv.trans (N := ∀ p : ps, P p) _ _
  -- There is only one Sylow subgroup for each p, so the inner product is trivial
  show (∀ p : ps, ∀ P : Sylow p G, P) ≃* ∀ p : ps, P p
  · -- here we need to help the elaborator with an explicit instantiation
    apply @MulEquiv.piCongrRight ps (fun p => ∀ P : Sylow p G, P) (fun p => P p) _ _
    rintro ⟨p, hp⟩
    haveI hp' := Fact.mk (Nat.prime_of_mem_primeFactors hp)
    letI := unique_of_normal _ (hn (P p))
    apply MulEquiv.piUnique
  show (∀ p : ps, P p) ≃* G
  apply MulEquiv.ofBijective (Subgroup.noncommPiCoprod hcomm)
  apply (bijective_iff_injective_and_card _).mpr
  constructor
  show Injective _
  · apply Subgroup.injective_noncommPiCoprod_of_independent
    apply independent_of_coprime_order hcomm
    rintro ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩ hne
    haveI hp₁' := Fact.mk (Nat.prime_of_mem_primeFactors hp₁)
    haveI hp₂' := Fact.mk (Nat.prime_of_mem_primeFactors hp₂)
    have hne' : p₁ ≠ p₂ := by simpa using hne
    apply IsPGroup.coprime_card_of_ne p₁ p₂ hne' _ _ (P p₁).isPGroup' (P p₂).isPGroup'
  show card (∀ p : ps, P p) = card G
  · calc
      card (∀ p : ps, P p) = ∏ p : ps, card (P p) := Fintype.card_pi
      _ = ∏ p : ps, p.1 ^ (card G).factorization p.1 := by
        congr 1 with ⟨p, hp⟩
        exact @card_eq_multiplicity _ _ _ p ⟨Nat.prime_of_mem_primeFactors hp⟩ (P p)
      _ = ∏ p in ps, p ^ (card G).factorization p :=
        (Finset.prod_finset_coe (fun p => p ^ (card G).factorization p) _)
      _ = (card G).factorization.prod (· ^ ·) := rfl
      _ = card G := Nat.factorization_prod_pow_eq_self Fintype.card_ne_zero

#align sylow.direct_product_of_normal Sylow.directProductOfNormal


variable (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [Fintype G]

theorem Cauchy_1 (hdvd : p ∣ Fintype.card G) : ∃ g : G, orderOf g = p := by
  exact exists_prime_orderOf_dvd_card p hdvd
  done

theorem sylow_card_eq_index_normaliser (hdvd : p ∣ Fintype.card G) (P : Sylow p G) [Fintype (Sylow p G)] : Fintype.card (Sylow p G) = Subgroup.index (Conjugate g P) := by



end Sylow
