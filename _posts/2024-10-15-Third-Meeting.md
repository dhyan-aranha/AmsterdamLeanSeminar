---
layout: post
title: Summary of 14/10/2024
---

In our third meeting we discussed the chapters: Functions and Sets of [Buzzard's course](https://github.com/ImperialCollegeLondon/formalising-mathematics-2024/). Our main focus was on sheet 3 of Functions and sheet 6 of Sets. 

The part of sheet 3 of functions which we focues on was to prove the follwing lemma

Lemma: There exists morphisms $$ f :X \rightarrow Y$$ and $$ g :Y \rightarrow Z$$ of sets such that the composition $$ g \circ f$$ is surjective but $$\ f$$ is not surjective. 

Actually at this point in the notes we have not yet been told how to think about sets so the statment we will actually prove will be about types:

```
¬∀ A B C : Type, ∀ (φ : A → B) (ψ : B → C), Surjective (ψ ∘ φ) → Surjective φ

```
If we were still just thinking about sets then we could consider the following composition:

$$ \{ a \} \underset{a \mapsto b}{\rightarrow} \{ b , c \} \underset{b,c \mapsto d}{\rightarrow} \{ d \}$$

Heres how this would go with types in Lean: We will define three inductive types X, Y and Z

```
inductive X : Type
  | a : X

```

Which we should think of as $$ X = \{ a \}$$.

```
inductive Y : Type
  | b : Y
  | c : Y 

```
Which should be thought of as $$ Y = \{ b ,c \}$$

and finally

```
inductive Z : type
  | d : Z

```
which is $$Z = \{ d \}$$.

Now we have to construct our functions $$f$$ and $$g$$:

```
def f : X → Y
  | X.a => Y.b
```
```
def g : Y → Z
  | Y.b => Z.d
  | Y.c => Z.d
```

The first result we need is that is that  " $$ b \neq c $$ ":

```
theorem Yb_ne_Yc : Y.b ≠ Y.c := by
intro h
  -- x ≠ y is definitionally equal to (x = y) → False
  cases h
```

Next, we should establish that the composition $$ g \circ f$$ is surjective

```
theorem gf_surjective : Surjective (g ∘ f) := by
intro Z.d
use X.a

```

Finally we are ready to prove the main result:

```
¬∀ A B C : Type, ∀ (φ : A → B) (ψ : B → C), Surjective (ψ ∘ φ) → Surjective φ
```

The following strategy was suggested by Pjotr: First we use the tactic "push_neg", which turns our goal into:

```
∃ A B C φ ψ, Surjective (ψ ∘ φ) ∧ ¬Surjective φ
```

We could now finish the proof in one line with an "exact < ....>" tactic except we need to prove:  ¬Surjective f, i.e. "f is not surjective". So lets do this

```
theorem f_not_surjective: ¬Surjective (f) := by
intro h1
specialize h1 Y.c
rcases h1 with ⟨X.a, p⟩
trivial
```

Now we can finish the proof of the main theorem with the following use of the exact tactic:

```
exact ⟨_, _, _, _, _, gf_surjective, f_not_surjective⟩.
```
All together this looks like:

```
¬∀ A B C : Type, ∀ (φ : A → B) (ψ : B → C), Surjective (ψ ∘ φ) → Surjective φ := by
push_neg
exact ⟨_, _, _, _, _, gf_surjective, f_not_surjective⟩
```

We spent the second half of the time working on sheet 6 of the chapter on Sets. The two proofs we discussed were of the following facts:

Lemma: $$id (S) = S$$

Which is formalized in lean as

```
example : id '' S = S

```

The reason for the notation " id '' " is because there is a term/type disagreement, that is to say writing something like "id S"  does not make sense: the fuction id : S → S, takes terms of S but S itself has type Set S. 

I presented a hacky proof of this which was streamlined in discussion. The final outcome was basically the same as Buzzards solution so I will not reproduce it here. 

The second statment we worked on was "taking images behaves well under composition"

Lemma: $$ g \circ f (S) = g ( f (S))$$

This statment formalizes to 

```
g ∘ f '' S = g '' (f '' S)
```
Pjotr presented a nice proof of this result which if I have time later I'll add. But basically you can do the bone-headed thing (my specialty) and deconstruct everything via the cases' tactic or you can think about all the quantifiers involved in the definitions beforehand and save alot of key strokes with rintro <..> 's and exact <...>'s. 

Let me just add, that it was pointed out by Andrés during the discussion that there is a very short proof of this theorem using the "simp" tactic:

```
 g ∘ f '' S = g '' (f '' S) := by
ext s
simp
```

Also, we saw a new useful tactic 

```
rwa [..]
```

which is a combination of the rewrite tactic followed by assumption tactic. (documentation for all these tactics can be found in Buzzards notes)





