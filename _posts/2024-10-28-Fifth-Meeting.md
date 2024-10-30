---
layout: post
title: Summary of 28/10/2024
---

In our fifth meeting we had a look at Section 07: Subgroups and Homorphisms and Section 08: Finitness. We spent most of the period discussing sheets 2 and 3 of Subgroups and Homomorphisms. 




We had a look at the following lemma:

Lemma: Suppose $$\varphi: G \rightarrow H$$ and $$\psi : H \rightarrow K$$ are group homomorphisms. If $$S$$ is a subgroup of $$G$$ then we have an equality: $$(\psi \circ \varphi)(S) = \psi (\varphi(S))$$. 

The formalization of this statment in Lean looks like:

```
example (φ : G →* H) (ψ : H →* K) (S : Subgroup G) : S.map (ψ.comp φ) = (S.map φ).map ψ 
```

In this example we see also an example of the use of [dot-notation](https://lean-lang.org/lean4/doc/struct.html#:~:text=The%20dot%20notation%20is%20convenient,to%20foo%20has%20type%20Point%20.) in Lean. Here is a nice solution that Jan explained to us

```
ext y
constructor
·  rintro ⟨_, h1, h2 ⟩
   exact ⟨φ _, ⟨_, h1, rfl⟩, h2⟩
·  rintro ⟨_, ⟨_, h1, rfl⟩, h2 ⟩
   exact ⟨_, h1, h2⟩
```

Next we discussed Sheet 3 of Subgroups and Homomorphisms and Thomas explained to us a slick and honest (i.e. without using the full force of the simp tactic, which already knows this result) proof of the following exercise

Lemma: Let $$N$$ be a normal subgroup of $$G$$. Then the Kernel of the quotient map $$ G \rightarrow G/N$$ is $$N$$. 

```
example : (mk' N).ker = N := by

ext a
rw [MonoidHom.mem_ker, ← (mk' N).map_one, eq_comm, mk'_eq_mk' N]
simp_rw [one_mul, exists_eq_right]
```

We ended the meeting with a small discussion lead by Pjotr about his frustration with the API for talking about finitness in Lean.
