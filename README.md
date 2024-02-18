# syl_thm_env

A project exploring and then extending the implementation of group theory in the functional formal verification language Lean4.

In formal written mathematics, A group $G$ is often defined to be a set $G$, endowed with a closed binary operation $\circ: G \times G \to G $, such that the following three properties hold

1.  Associativity: $\; \; \; \; \forall a,b,c\in G, \; a \circ (b \circ c) = (a \circ b) \circ c $
2.  Identity: $ \; \; \; \; \; \; \; \; \; \;\exists 1_G \in G: \; \forall g \in G, \; 1_G \circ g = g \circ 1_G = g $
3.  Inverses: $ \; \; \; \; \; \; \; \; \; \;\forall g \in G, \exists g^{-1} \in G: \;  g \circ g^{-1} = g^{-1} \circ g = 1_G $

For formal verification, and in particular in this case, and also the setting of functional programming it is instead advisable to build up to the structure of a group recursively, through three intermediate algebraic structures. We do so by defining the following: 

    Setoid: A set, equipped with a closed binary operation on itself.

    Semigroup: A setoid, with property 1 (Associativity)

    Monoid: A semigroup, with the addition of property 2 (Identity)

Our new definition of a group then follows...

    Group: A monoid, with the addition of property 3 (Inverses)

This abstraction allows us to more precisely manipulate the properties of groups and implement inheritance in the type system of Lean.

## Sylow's Theorems

In the following, G denotes a finite group, and p a prime:

We define the following:

    p-Subgroup: A subgroup with order p^i for some natural number i
    Sylow p-Subgroup: A p-subgroup with i maximal, i.e its index in G is not divisible by p
    &Syl_p(G)$: The set of Sylow p-subgroups in G

Insert theorems 1-4 here:
1. Existence: If a prime p divides G, there is a Sylow p-subgroup of G
2. Conjugacy: Any two Sylow p-subgroups of a group G are conjugate
3. Containment: Any p-subgroup of G is contained within a Sylow p-subgroup
4. Congruency: The number of Sylow p-subgroups is congruent to 1 modulo p, that is $|Syl_p(G)| \equiv 1 (\mod p)$

The proofs we implemented are based on the Lecture Notes for MA3K4 Introduction to Group Theory by Gareth Tracey. 

To prove theorems 1 and 4, we require two number theoretic lemmas as follows:

Lemma 3.3 ___
Proposition 3.4 ____

We then prove the result.

To prove theorems 2 and 3, we require one intermediary proposition about the conjugation of Sylow p-subgroups

Prop 3.5 ___

We then prove the result.

We also went on to prove a few consequences of Sylow's Theorems, including the following:

Corollary 3.7

Corollary 3.8

## Sylow's Game 

We then used our implementation to give some examples of proving the simplicity, or non-simplicity, of some finite groups of low order, including the following:

A group of order 20 is simple:

A group of order ? is non-simple:

## Progress Report / Evaluation

During the course of the project, our goals shifted many times, and it became apparent after a great deal of effort that programming a unique and extensive proof of Sylow's Theorem's with only minimal use of dependencies was too ambitious a goal, and we have ultimately been unable to reach some of the intended goals of the project. 

However, as a group, we have expended a vast amout of time and effort furthering our understanding of Lean, and while we have not been able to do everything we originally intended to do, we still have a lot to show for our efforts.

Firstly, we have commented extensively on the Sylow.lean file, and have worked very hard to understand the intricacies of how Sylow's theorem's are set out in Mathlib.

Secondly, we have an initial skeleton, titled Sylow_Skeletonlean which is filled out with attempted proofs, some of which more complete then others. 

We then have a second skeleton, New_Skeleton.lean, which is largely empty, but contains some initial attempts to redefine key concepts.

The final piece of work making up our submission is the file Sylow_Corollaries.lean, which contains attempted proofs deduced from the theorems and definitions contained in the Sylow.lean file. These include Cauchy's theorem, as well as classifications for specific families of finite groups. 

We understand that this submission is somewhat unorthodox, but our hope is that you will find some merit in it's constituent parts, though it may not form a cohesive whole.

Tom, Antonina & Roshan






