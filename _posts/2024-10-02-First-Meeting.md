---
layout: post
title: Summary of 30/09/2024
---


In this meeting Lenny, told us a bit about type theory and how it is implemented in lean. Here is what I took away (all inaccuracies are mine!):

A side effect of doing our mathematics in ZFC is that we have certain "junk theorems":

$$\mathbf{R} \notin \pi $$, $$ 2 \in (0,1)$$, etc. 

That is to say, they are true statements based on our foundations but they are nonsensical. 

An advantage of doing mathematics in type theory is that:

<center> Everything is a term of a unique (!) type. </center>

The notation for this is:

 <center> $$ x : X $$</center>

which should be read as $$x$$ is a term of type $$X$$. This excludes the junk theorems from above from our theory because it longer makes sence to ask, for example, if $$\mathbb{R} \in \pi$$. 


In Lean there is a hierarchy of types as follows: At the top there is a chain of "type universes":

$$ \text{Type} : \text{Type 1}, \text{Type 1} : \text{Type 2}, ....$$

Things like the real and natural numbers which are themselves types are encoded as terms in $$\text{Type}$$:

$$\mathbf{R}$$ : Type, $$\mathbf{N}$$ : Type, ...

At the bottom are things like $$\pi$$ and $$3$$ which only make sense as terms of a type:

$$\pi$$ : $$\mathbf{R}$$, $$3$$ : $$\mathbf{N}$$,...

Another feature of type theory is that there is the type

$$ \text{Prop} : \text{Type} $$.

The terms of $$\text{Prop}$$ are <em> assertions </em> which themselves are types that have terms which are their <em>proofs</em>. For example, the statement of the fermat's last theorem (FLT) is a term in $$\text{Prop}$$:

$$\text{FLT} : \text{Prop}$$

and the terms of $$\text{Flt}$$ are its proofs. A proposition is <em> true </em> if and only if it has a term i.e. a proof. When Lean compiles it treats all proofs of a proposition as equal via the axiom of of <em> proof irrelevance </em> which states:

<center> If p,q : P : Prop, then p = q. </center>


We also discussed how to construct new types:

1) Function types

2) Inductive types

3) Product types

4) Sum Types

5) Quotient Types

Lastly, we discussed the Curry-Haskell correspondence between logic and type theory here is a small sample

Logic                   |Type                   | 
------------------------|-----------------------|
False                   | False ($$\emptyset$$) | 
True                    | True ($$ {\bullet}$$) |
$$ P \wedge Q$$         | $$ P \times Q $$      |
$$ P \implies Q $$      | $$ P \rightarrow Q$$  |
Universal quantificaiton|Dependent product type |

