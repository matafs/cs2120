import data.set

/-
Exercise: Prove that for any set, L, L ∩ L = L.
-/
example : ∀ {α : Type} (L : set α), L ∩ L = L := 
begin
  intros α L,
  apply set.ext,
  assume x,
  split,
  -- forward
  assume h,
  cases h with l r,
  exact l,
  -- backward
  assume k,
  apply and.intro,
  exact k,
  exact k,
end

/-
Exercise: Give a formal statement and proof, then an 
English language proof, that the union operator on 
sets is commutative.

let x be an element of A ∪ B. Then x is an element of A or x is an element of B.
Then by definition of union x is an element of B ∪ A. Therefore A ∪ B ⊆ B ∪ A. 
Let x be an element of A ∪ B. Then x is an element of A or x is an element of B. 
Then by definition of union x is an element of A ∪ B. Therefore B ∪ A ⊆ A ∪ B. 
Hence A ∪ B = B ∪ A.
-/
example : ∀ {α : Type} (A B: set α), A ∪ B = B ∪ A := 
begin
  intros α A B,
  apply set.ext,
  assume x,
  split,
  -- forward
  assume h,
  cases h with l r,
  apply or.intro_right,
  exact l,
  apply or.intro_left,
  exact r,
  -- backward
  assume k,
  cases k with l r,
  apply or.intro_right,
  exact l,
  apply or.intro_left,
  exact r,
end

/-
Exercise: Prove that ⊆ is reflexive and transitive.
Give a formal statement, a formal proof, and an English
language (informal) proof of this fact.

reflexive
let x be an element of A. Since x is an element of A implies x is an element of A, A ⊆ A.

transitive
let x be an element of A. Assume A ⊆ B and B ⊆ C. Since A subset of B x is an element of B 
and since B is a subset of C x is an element of C. Since x ∈ A and x ∈ C, A ⊆ C. 
Therefore if A ⊆ B and B ⊆ C then A ⊆ C.
-/
--reflexive
example : ∀ {α : Type} (A : set α), A ⊆ A := 
begin
  intros α A,
  assume x,
  assume h : x ∈ A,
  exact h,
end
-- transitive
example : ∀ {α : Type} (A B C: set α), A ⊆ B ∧ B ⊆ C → A ⊆ C := 
begin
  intros α A B C,
  assume h,
  assume x,
  assume xA,
  have AsubB := and.elim_left h,
  have BsubC := and.elim_right h,
  have xB := AsubB xA,
  have xC := BsubC xB,
  exact xC,
end
/-
Exercise: Prove that ∪ and ∩ are associative.
Give a formal statement, a formal proof, and an 
English language (informal) proof of this fact.
-- Union associative
Let x be an element of (A ∪ B) ∪ C. Then x ∈ (A ∪ B) or C. If x ∈ (A ∪ B) then
x ∈ A or B. If x ∈ A then x ∈ A ∪ (B ∪ C). If x ∈ A then x ∈ (B ∪ C). Therfore 
x ∈ A ∪ (B ∪ C). And if x ∈ C then x ∈ (B ∪ C) and so x ∈ A ∪ (B ∪ C). Therefore 
(A ∪ B) ∪ C ⊆ A ∪ (B ∪ C). 
In the other direction let x be be an element of A ∪ (B ∪ C). Then x ∈ A or (B ∪ C). 
If x ∈ A then x ∈ (A ∪ B) and so x ∈ (A ∪ B) ∪ C. And if x ∈ (B ∪ C) then x ∈ B or C.
If x ∈ B then x ∈ (A ∪ B) and so x ∈ (A ∪ B) ∪ C. And if x ∈ C then x ∈ (A ∪ B) ∪ C.
Hence A ∪ (B ∪ C) ⊆ (A ∪ B) ∪ C.
Therfore (A ∪ B) ∪ C = A ∪ (B ∪ C)

-- intersection associative
x is in (A ∩ B) ∩ C iff x ∈ (A ∪ B) and C. And x ∈ (A ∪ B) iff x ∈ A and x ∈ B.
Similarly, x ∈ A ∪ (B ∪ C) iff x ∈ A and B and C. Since A ∪ (B ∪ C) and (A ∩ B) ∩ C
have the same elements, x ∈ A ∪ (B ∪ C) iff x ∈ (A ∪ B) ∪ C. Therfore 
(A ∩ B) ∩ C = A ∩ (B ∩ C).
-/
example : ∀ {α : Type} (A B C: set α), (A ∪ B) ∪ C = A ∪ (B ∪ C) := 
begin
  intros α A B C,
  apply set.ext,
  assume x,
  split,
  -- forward
  assume h,
  cases h with l r,
  apply or.elim l,
  assume xA,
  apply or.intro_left,
  exact xA,
  assume xB,
  apply or.intro_right,
  apply or.intro_left,
  exact xB,
  apply or.intro_right,
  apply or.intro_right,
  exact r,
  -- backward
  assume h,
  cases h with l r,
  apply or.intro_left,
  apply or.intro_left,
  exact l,
  cases r with l r,
  apply or.intro_left,
  apply or.intro_right,
  exact l,
  apply or.intro_right,
  exact r,
end
example : ∀ {α : Type} (A B C: set α), (A ∩ B) ∩ C = A ∩ (B ∩ C) := 
begin 
  intros α A B C,
  apply set.ext,
  assume x,
  split,
  -- forward
  assume h,
  apply and.intro,
  cases h with l r,
  exact and.elim_left l,
  apply and.intro,
  cases h with l r,
  exact and.elim_right l,
  cases h with l r,
  exact r,
  -- backward
  assume h,
  apply and.intro,
  apply and.intro,
  cases h with l r,
  exact l,
  cases h with l r,
  exact and.elim_left r,
  cases h with l r,
  exact and.elim_right r,
end

/-
Assignment: read (at least skim) the Sections 1 and 2 of 
the Wikipedia page on set identities: 
https://en.wikipedia.org/wiki/List_of_set_identities_and_relations 
There, , among *many* other facts, you will find definitions 
of left and right distributivity. To complete the remainder
of this assignment, you need to understand what it means for 
one operator to be left- (or right-) distributive over another. 
-/


/-
Exercise: Formally state and prove both formally and 
informally that ∩ is left-distributive over ∩.

let x be an element of A ∩ (B ∩ C). Thus x ∈ A and B and C. Thus x ∈ (A ∩ B) and
x ∈ (A ∩ C). Thus x ∈ (A ∩ B) ∩ (A ∩ C). Therfore A ∩ (B ∩ C) ⊆ (A ∩ B) ∩ (A ∩ C).
In the other direction
let x be an element of (A ∩ B) ∩ (A ∩ C). Thus x ∈ (A ∩ B) and (A ∩ C). Thus x ∈ A 
and B and C. Thus Thus x ∈ A and (B ∩ C). Thuse x ∈ A ∩ (B ∩ C).Therfore 
(A ∩ B) ∩ (A ∩ C) ⊆ A ∩ (B ∩ C).
Hence A ∩ (B ∩ C) = (A ∩ B) ∩ (A ∩ C).
-/
example : ∀ {α : Type} (A B C: set α), A ∩ (B ∩ C) = (A ∩ B) ∩ (A ∩ C) := 
begin
  intros α A B C,
  apply set.ext,
  assume x,
  split,
  -- forward
  assume h,
  apply and.intro,
  apply and.intro,
  exact and.elim_left h,
  cases h with l r,
  exact and.elim_left r,
  apply and.intro,
  exact and.elim_left h,
  cases h with l r,
  exact and.elim_right r,
  -- backward
  assume h,
  apply and.intro,
  cases h with l r,
  exact and.elim_left l,
  apply and.intro,
  cases h with l r,
  exact and.elim_right l,
  cases h with l r,
  exact and.elim_right r,
end

/-
Exercise: Formally state and prove both formally 
and informally that ∪ is left-distributive over ∩.

Let x be an element of A ∪ (B ∩ C). Thus x ∈ A or (B ∩ C). If x ∈ A then x ∈ (A ∪ B) 
and (A ∪ C). Thus x ∈ (A ∪ B) ∩ (A ∪ C). If x ∈ (B ∩ C) then x ∈ B and C. Thus 
x ∈ (A ∪ B) and (A ∪ C). Thus x ∈ (A ∪ B) ∩ (A ∪ C). Therfore A ∪ (B ∩ C) ⊆ (A ∪ B) ∩ (A ∪ C).
In the other direction.
Let x be an element of (A ∪ B) ∩ (A ∪ C). Thus x ∈ (A ∪ B) and (A ∪ C). Thus x ∈ A. 
Thus x ∈ A ∪ (B ∩ C). Therefore (A ∪ B) ∩ (A ∪ C) ⊆ A ∪ (B ∩ C).
Hence A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C).
-/

example : ∀ {α : Type} (A B C: set α), A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) := 
begin
  intros α A B C,
  apply set.ext,
  assume x,
  split,
  -- forward
  assume h,
  apply and.intro,
  cases h with l r,
  apply or.intro_left,
  exact l,
  apply or.intro_right,
  exact and.elim_left r,
  cases h with l r,
  apply or.intro_left,
  exact l,
  apply or.intro_right,
  exact and.elim_right r,
  -- backward
  assume h,
  cases h with l r,
  cases l with a b,
  apply or.intro_left,
  exact a,
  cases r with a c,
  apply or.intro_left,
  exact a,
  apply or.intro_right,
  exact and.intro b c,
end
