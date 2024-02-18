# syl_thm_env

A project exploring and then extending the implementation of group theory (more specifically Sylow's Theorems) in the functional formal verification language Lean4.

In Mathlib, Groups are defined on top of three intermediate weaker algebraic structures. This helps results to be even more general, these are as follows. 

    Setoid: A set, equipped with a closed binary operation on itself.

    Semigroup: A setoid, with associativity

    Monoid: A semigroup, with an identity element

Our new definition of a group then follows:

    Group: A monoid, with inverses for every element.

This abstraction allows us to more precisely manipulate the properties of groups and implement inheritance in the type system of Lean.

## Sylow's Theorems

In the following, G denotes a finite group, and p a prime:

We define the following:

p-Subgroup: A subgroup with order p^i for some natural number i

Sylow p-Subgroup: A p-subgroup with i maximal, i.e its index in G is not divisible by p

$Syl_p(G)$: The set of Sylow p-subgroups in G

The norwegian mathemitician Peter Ludwig Sylow first proposed the following four theorems in 1872, which were later proven many times in vastly different ways.

1. Existence: If a prime p divides G, there is a Sylow p-subgroup of G
2. Conjugacy: Any two Sylow p-subgroups of a group G are conjugate
3. Containment: Any p-subgroup of G is contained within a Sylow p-subgroup
4. Congruency: The number of Sylow p-subgroups is congruent to 1 modulo p, that is $|Syl_p(G)| \equiv 1\mod p$

The proofs we plan to implement are based on the Lecture Notes for MA3K4 Introduction to Group Theory by Gareth Tracey. 

To prove theorems 1 and 4, we require the following lemma from number theory:

Lemma 3.3: Let $p$ be prime, and let n and m be coprime integers. Then the following holds.

(i) $ \forall 1\le i \le p-1, \; \; p \mid \binom{p}{i} $, and
(ii) $\binom{p^nm}{p^n} \equiv m \mod p$

A proof by Wielandt then uses this lemma, as well as the orbit stabiliser theorem, and examines the conjugacy classes of the action, to determine that it cannot have size 0 (there exists a Sylow p subgroup), and instead has size equivalent to 1 mod p.

To prove theorems 2 and 3, we require one intermediary proposition about the conjugation of Sylow p-subgroups

Prop 3.5: Let $H \le G$ and $P \in Syl_p(G)$, Then $\exists g \in G$ such that $H \cap gPg^{-1} \in Syl_p(H) $


The result follows by applying this proposition to seperate Sylow p subgroups of G.

We also intend to prove a few consequences of Sylow's Theorems, including: 

Corollary 3.7: $\forall P \in Syl_p(G)$:

(i) $|Syl_p(G)| = |G : N_G(P)|$

(ii)$|Syl_p(G)|$ divides $ |G|/|G|_p$, where $G|_p$ denotes the largest power of p which divides the order of g

(iii) $P \trianglelefteq G \iff |Syl_p(G)| = 1 $  

aswell as 

Cauchy's Theorem: If $p \mid |G|$, then $\exists g \in G$ such that $|g| = p$, Furthermore, the number of such elements is congruent to $-1 \equiv \mod p$

## Sylow's Game 

Our plan is then to use our implementation to give some examples of proving the simplicity, or non-simplicity, of some finite groups of low order, including the following:

A group of order 20 is not simple

A group of order 462 is not simple

## Group Classification 

A final target of our project is to prove some basic results about classifying infinite families of groups. One example of such a result is the following: 

Lemma 4.14:  Let $p < q$ be primes such that $p \nmid (q-1) $ and $G$ a group of order $pq$. Then $G \cong C_{pq}$, the cyclic group of order $pq$.

## Individual Contributions

Tosia:

Roshan:

Tom: I orchestrated a lot of the technical requirements for the project, managing the git repository and setting up cloud infrastructure for remote working on gitpod. This was originally very error prone but eventually worked consistently. I instructed my group on how to use git, and the basic concepts of branches, pushing and pulling etc. I commented hundreds of lines of mathlib code, and discussed what I found with my group to help further our understanding on how Mathlib efficiently implements Group Theory in the context of lean, explaining things like how type coercion was used to convert Sylow groups to subgroups, and how the algebraic structures like monoids and semigroups defined under groups. I streamlined and commented on lots of our code, to help make our work more legible and concise. I also wrote several drafts of the README.md file, including a lot of typesetted maths in Latex, and ensured references to our source material on group theory were accurate.

## Progress Report / Evaluation

During the course of the project, our goals shifted many times, and it became apparent after a great deal of effort that programming a unique and extensive proof of Sylow's Theorem's with only minimal use of dependencies was too ambitious a goal, and we have ultimately been unable to reach some of the intended goals of the project. 

However, as a group, we have expended a vast amout of time and effort furthering our understanding of Lean, and while we have not been able to do everything we originally intended to do, we still have a lot to show for our efforts.

Firstly, we have commented extensively on the Sylow.lean file, and have worked very hard to understand the intricacies of how Sylow's theorem's are set out in Mathlib.

Secondly, we have an initial skeleton, titled Sylow_Skeletonlean which is filled out with attempted proofs, some of which more complete then others. 

We then have a second skeleton, New_Skeleton.lean, which is largely empty, but contains some initial attempts to redefine key concepts.

The final piece of work making up our submission is the file Sylow_Corollaries.lean, which contains attempted proofs deduced from the theorems and definitions contained in the Sylow.lean file. These include Cauchy's theorem, as well as classifications for specific families of finite groups. 

We wanted to makes some extra comments regarding the classification proof. Roshan and Antonina eventually managed to prove this theorem completely but this was only after a multitude of unsucessful attempts. One example of an issue we ran into, was that for a normal group P, we have $gP = Pg \; \; \forall g \in G$, and we thought for some reason this implies all group elements of P commute with the rest of the group, but this is in fact incorrect. Another error was proving that P is a normal subgroup of P, thinking we had shown that the group P was normal in G. We managed to correct our thinking by paying close attention to our source material, and the specific proofs we wanted to formalise, making note of every single step and what assumptions are used. This eventually helped to clarify how the results should be formalised. 

Throughout our attempts we have had to reorder what we proved to make sure we were using the correct type classes as we coerce the types of P, Q to a Sylow p G and Sylow q G respectively. We learnt it was best to split our problems into smaller subgoals and have them be their own separate theorems, ensuring that the final proof was more concise and unnecessary clutter was avoided. 

We understand that this submission is somewhat unorthodox, but our hope is that you will find some merit in it's constituent parts, though it may not form a cohesive whole.

Tom, Antonina & Roshan






