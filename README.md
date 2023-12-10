# syl_thm_env

A project exploring and then extending the implementation of group theory in the functional formal verification language Lean4.

In formal written mathematics, A group $G$ is often defined to be a set $G$, endowed with a closed binary operation $\circ: G \times G \to G $, such that the following three properties hold

1.  Associativity: $\; \; \; \; \forall a,b,c\in G, \; a \circ (b \circ c) = (a \circ b) \circ c $
2.  Identity: $ \; \; \; \; \; \; \; \; \; \;\exists 1_G \in G: \; \forall g \in G, \; 1_G \circ g = g \circ 1_G = g $
3.  Inverses: $ \; \; \; \; \; \; \; \; \; \;\forall g \in G, \exists g^{-1} \in G: \;  gg^{-1} = g^{-1}g = 1_G $

For formal verification, and in paticular in this case, nalso the setting of functional programming it is instead advisable to build up to the structure of a group recursively, through three intermediate structures. We do so by defining the following: 

    Setoid: A set, equipped with a closed binary operation on itself.

    Semigroup: A setoid, with property 1 (Associativity)

    Monoid: A semigroup, with the addition of property 2 (Identity)

Our new definition of a group then folllows...

    Group: A monoid, with the addition of property 3 (Inverses)

This abstraction allows us to more precisely manipulate the properties of groups, and allows us to implement inheritance in the type system of Lean.

## Sylow's Theorems

Insert theorems 1-4 here:

The proofs we have implemented are based around the Lecture Notes for MA3K4 Introduction to Group Theory by Gareth Tracey. 

To prove theorems 1 and 4, we require two number theoretic lemmas as follows:

(Lemmas here)

We then prove the result.

To prove theorems 2 and 3, we require one intermediary proposition about the conjugation of Sylow p-subgroups

(Prop here) 

We then prove the result.

We also went on to prove a few consequences of Sylow's Theorems, including the following:

(Thm)

(Another thm)

## Sylow's Game 

We then used our implementation to give some examples of proving the simplicity, or non-simplicity, of some finite groups of low order, including the following:

A group of order 20 is simple:

A group of order ? is non-simple:



