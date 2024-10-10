---
layout: post
title: Summary of 07/10/2024
---

In our second meeting we discussed the chapter on the real numbers in [Kevin Buzzard's course](https://github.com/ImperialCollegeLondon/formalising-mathematics-2024/). We focused most of our attention on sheets 3 and 5.

Sheet 3 is about formalizing the notion of convergent sequence of real numbers. This can be formalized as follows:

```
def TendsTo (a : ℕ → ℝ) (t : ℝ) : Prop :=
  ∀ ε > 0, ∃ B : ℕ, ∀ n, B ≤ n → |a n - t| < ε
```

The first problem we discussed was to formalize the proof of the following lemma:

Lemma: If $$\{ a_n\}_n $$ converges to $$t$$ then $$ \{ a_n + c\}_n $$ converges to $$t+c$$. 

Using, TendsTo, we can formalize this statement as 

```
theorem tendsTo_add_const {a : ℕ → ℝ} {t : ℝ} (c : ℝ) (h : TendsTo a t) :
    TendsTo (fun n => a n + c) (t + c)
```


here is the first proof that we came up with:

```
  intro ε hε 
  cases' h ε hε with B h1
  use B
  norm_num
  exact h1
```

It turns out that one does not need to unwrap things via the intro and cases' tactics and it was pointed out by Shin that there is a much more efficient proof:

```
  rw[tendsTo_def] at *  -- This applies the rewrite to all hypotheses and the goal.
  norm_num
  exact h
```
The magic here is that it seems norm_num tactic can "go through" quanitfiers.

Next we tried to prove: 

Lemma: If the sequence $$\{a_n\}_n $$ converges to $$ t$$ then the sequence $$ \{ -a_n \}_n$$ converges to $$-t$$.  

which formalizes to the statement:
```
lemma tendsTo_neg_const {a : ℕ → ℝ} {t : ℝ} (ha : TendsTo a t) : 
    TendsTo (fun n => -a n) (-t)
```

Here was our solution:

```
rw [tendsTo_def]
intro ε hε 
specialize ha ε hε 
cases' ha with B hB
use B
intro n hn
specialize hB n hn
rw[← abs_neg]  -- The tactic abs_neg is a proof of |-x| = |x|.
ring_nf
exact hB
```
Lastly we discussed the following lemma from from sheet 5

Lemma: If $$\{ a_n\}$$ converges to $$t$$ and $$\{ b_n \}$$ converges to  $$u$$ then $$ \{a_n + b_n \}$$ converges to $$t + u$$. 

Which formalizes to the statment:

```
theorem tendsTo_add {a b : ℕ → ℝ} {t u : ℝ} (ha : TendsTo a t) (hb : TendsTo b u) :
    TendsTo (fun n ↦ a n + b n) (t + u) :=
```

The proof in Buzzard's notes does not explicitly use the triangle inequality. 
However Lenny explained to us a formalization which is does use the triangle inequality and probably matches more closely how human mathematicians
would prove the statement. 

```
 rw [tendsTo_def] at *
 intro ε hε 

 specialize ha (ε/2) (by linarith)
 specialize hb (ε/2) (by linarith)

 rcases ha with ⟨X, hX⟩
 rcases hb with ⟨Y, hY⟩

 use max X Y

 intro n hn

 rw [max_le_iff] at hn
 specialize hX n hn.1
 specialize hY n hn.2


 calc
      |a n + b n - (t + u)| = |a n - t + (b n - u)| := by rw [add_sub_add_comm]
                          _ ≤ |a n - t| + |b n - u| := abs_add _ _
                          _ < ε/2 + ε/2 := by linarith
                          _ = ε 
```
Through Lenny's code we also learned about a new tactic called <b> calc </b> and a very useful website called [moogle](https://www.moogle.ai) which is a search tool for mathlib, which for example can help you locate the triangle inequality!

