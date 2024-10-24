---
layout: post
title: Summary of 21/10/2024
---

During this meeting we had a look at sections Groups and Orderings and Lattices in [Buzzard's notes](https://github.com/ImperialCollegeLondon/formalising-mathematics-2024/). 

In Sheet 2 of Groups we encountered two new concepts: The notions of "class" and "instance". If you go to the definition of group in mathlib you will find

```
class Group (G : Type u) extends DivInvMonoid G where
  protected mul_left_inv : ∀ a : G, a⁻¹ * a = 1
```

That is groups are defined as a class in lean. In Sheet 2 we defined a an apriori weaker object called WeakGroup 

```
class WeakGroup (G : Type) extends One G, Mul G, Inv G : Type where
  mul_assoc : ∀ a b c : G, a * b * c = a * (b * c)
  one_mul : ∀ a : G, 1 * a = a
  inv_mul_self : ∀ a : G, a⁻¹ * a = 1

```
Which has fewer axioms than the class group. Note: you can't see all the axioms used in the definition 
of group because they are hidden in the "extends DivInvMonoid G".  Most of the sheet is about proving that infact the obvious axioms:

mul_one : a * 1 = a 
mul_inv_self: a * a⁻¹ = 1 

follow from these. In particular weak groups are groups. After this Lenny explained an example about how to use instances: Now that we know weak groups are groups we can use weak groups as an "instance" of groups:

```
variable (G : Type)

instance [WeakGroup G] : (Group G) where
mul_assoc := WeakGroup.mul_assoc
one_mul := WeakGroup.one_mul
mul_one := WeakGroup.mul_one
mul_left_inv := WeakGroup.inv_mul_self
```
Now if we give our variable G the structure of WeakGroup

```
variable [WeakGroup G]
```
then lean already knows by type-class inference that G is infact a group:

```
lemma WeakGroup_is_Group : Group G:= by
infer_instance
```

Moreover if we #print WeakGroup_is_Group then this is what is shown in the infoview:

```
⊢ (G : Type) → [inst : WeakGroup G] → Group G
```

As another test of type-class inference we can prove the following theorem

Theorem: Let H be a weak group. Suppose that for all h in H, h*h = 1, then H is abelian.

On Sheet we already proved this theorem for groups:

```
theorem commutative_of_involutive (h : ∀ g : G, g * g = 1) : 
∀ g h : G, g * h = h * g := by

 have useful : ∀ g : G, g = g⁻¹ := by
    intro g
    rw [← eq_comm, ← mul_eq_one_iff_inv_eq]
    exact h g

  intro g h
  rw [useful (g * h), mul_inv_rev, ← useful g, ← useful h]

```
After importing this result to our current sheet via: 

```
import FormalisingMathematics2024.Section05groups.Sheet1
```
We can now prove our theorem

```
theorem check_inference (H:Type) [WeakGroup H] (h_inv: ∀ x : H, x * x = 1):
∀ x y : H, x * y = y * x := by

apply commutative_of_involutive H h_inv
```

We again see here that lean already knows that weak group is a group and will automatically apply results proved for groups to weak groups. 


In sheet 3, which was on the topic of subgroups and homomorphisms,  Pjotr explained a very nice proof of the following fact

Lemma: Let H be a subgroup G, suppose a, b, c, are elements of H. Then a * b⁻¹ * 1 * (a * c) ∈ H

The naive proof can take many lines of writing the same apply tactic over and over again. However if one uses
the repeat tactic there is a very short proof


```
example (a b c : G) (ha : a ∈ H) (hb : b ∈ H) (hc : c ∈ H) :
    a * b⁻¹ * 1 * (a * c) ∈ H := by

have hbinv := H.inv_mem hb
have hone := H.one_mem
repeat apply H.mul_mem <;> try assumption

```

Finally we had a look at sheet 4 of Orderings and Lattices and Dion explained the following example to us

```
example : a ≤ ⊥ ↔ a = ⊥ := by
repeat rw [← sSup_empty]
constructor
intro h
have hs : sSup ∅ ≤ a := by
  apply sSup_le
  intro b hb
  tauto
exact le_antisymm h hs

rintro rfl
rfl
```

