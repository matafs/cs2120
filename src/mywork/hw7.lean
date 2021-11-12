import data.set
import tactic.ring

namespace relation

-- PRELIMINARY SETUP

/-
Preliminary set up. For the rest of this file,
we specify an arbitrary binary relation, r, on
an arbitrary type, β, as a two-place predicate, 
with infix notation x ≺ y for (r x y). One can
pronounce these expressions in English as "x is
related to y".
-/
variables {α β : Type}  (r : β → β → Prop)
local infix `≺` : 50 := r  


/-
The default Lean libraries are missing definitions
for the assympetric property of relations and for
the notion of a powerset. We define these terms for
use in the rest of this file.
-/
def asymmetric := ∀ ⦃x y⦄, x ≺ y → ¬ y ≺ x
def powerset (s : set β) := { s' | s' ⊆ s}


-- PROBLEMS

/- 
#1: Give both a formal and an English-language proof. Then
answer the question, is the proposition true if you remove
the first condition, that β is inhabited? Briefly explain
your answer (in English).

> is an assymetric relation. Thus a is not > a. Therfore is r is asymmetric then 
it is not reflexive.
-/
example : (∃ (b : β), true) → asymmetric r → ¬reflexive r :=
begin
  intros e ar,
  unfold reflexive,
  assume a,
  unfold asymmetric at ar,
  cases e,
  have w:= a e_w,
  have t:= ar w,
  contradiction, 
end



/-
#2. Logic, like programming, is subtle. It's very easy for humans
to miss subtle corner cases. As an example, today I ran across
a problem in a textbook by Paul Traiger, a professor emeritus
of philosophy and cognitive science at Occidental College. He
asks students to prove that if a relation is both transitive and 
reflexive that it cannot be anti-symmetric. See the question at
the very bottom of the page here:
https://sites.oxy.edu/traiger/logic/exercises/chapter13/properties_of_relations_exercise.html

Is the conjecture actually logically valid? If not, what condition 
needs to be added to make it so? Try prove this/his version of the
conjecture, as articulated slightly differently below. If you get
stuck, then you need to figure out an additional condition that needs 
to be added as a premise to make the proposition true. In that case,
add the premise and then show that the updated conjecture is true.
-/
example : (∃ (b : β), true) → transitive r → reflexive r → ¬ asymmetric r :=
begin
  unfold transitive reflexive asymmetric,
  assume b trans ref,
  assume asymm,
  cases b,
  have q:= ref b_w,
  have qb:= asymm q,
  contradiction,
end





/-
#3: Prove that the subset relation on the powerset of any
set, s, is antisymmetric. Formally state and prove, and
then give an informal proof of, this proposition.

assume a ⊆ b and b ⊆ a. Assume x is an element of a, then x is an element of b. In the 
other direction, assume x is an element of b then x is an elemnt of a because b ⊆ a. 
Since x ∈ a and x ∈ b, therefore a = b.
-/
example : ∀ (s : set β) 
            (s1 s2 ∈ powerset s), 
            s1 ⊆ s2 → 
            s2 ⊆ s1 → 
            s1 = s2 :=
begin
  unfold powerset,
  assume a a1 a2,
  assume h1 h2 h3,
  assume h4,
  apply set.ext _,
  assume x,
  split,
  -- forward
  assume h,
  have q:= h3 h,
  exact q,
  -- backward
  assume h,
  have q:= h4 h,
  exact q,
  
end


/-
Given two natural numbers, n and m, we will say that m divides n
if there is a natural number, k, such that n = k*m. Here's a formal
definition of this relation.
-/
def divides (m n : ℕ) := ∃ k, n = k * m


/- 
#4: Formally and informally state and prove each of the following
propositions. Remember that the ring tactic is useful for producing
proofs of simple algebraic equalities involving + and *. You can use
the phrase, "by basic algebra" when translating the use of this tactic
into English. (Or if you wanted to be truly Hobbit-like you could say 
"by the ring axioms!")
-/

/-
assume n is a natural number. Then if k = n, n=n*1 is true by basic algebra.
-/
-- A: For any n, 1 divides n.
example : ∀ n, divides 1 n :=
begin
  assume n,
  unfold divides,
  apply exists.intro n,
  ring,
end
/-
assume n is a natural number. Then if k = 1, n=n*1 is true by basic algebra.
-/
-- B. For any n, n divides n
example : ∀ n, divides n n :=
begin
  assume n,
  unfold divides,
  apply exists.intro 1,
  ring,
end
/-
assume n is a natural number. Then if k = 1, n=n*1 is true by basic algebra.
-/
-- #C. prove that divides is reflexive 
example : reflexive divides :=
begin
  unfold reflexive divides,
  assume n,
  apply exists.intro 1,
  ring,
end 
/-
assume x,y,z are natural numbers. assume y= k1*x and z=k2*y then if k = k1*k2, z = k*x
can be rewritten as k2*k1*x = k1*k2*x which is true by basic algebra.
-/

-- #D. prove that divides is transitive
example : transitive divides :=
begin
  unfold transitive divides,
  assume x y z,
  assume h,
  assume h2,
  cases h,
  cases h2,
  apply exists.intro (h_w * h2_w),
  rw h2_h,
  rw h_h,
  ring,
end 

/- 
E. Is divides symmetric? if yes, give a proof, otherwise 
give a counterexample and a brief explanation to show that 
it's not.
-/

-- no 1 divides 2 but there is no natural number k to make 2 divides 1 true.

/- 
#F. Prove that divides is antisymmetric. 

if a divides b and b divides a then a = b. Since a divides b and b divides a 
is only true when a = b it can be said that divides is antisymmetric.
-/
example : anti_symmetric divides := 
begin 
  unfold anti_symmetric,
  unfold divides,
  assume x y,
  assume h,
  assume h2,
  cases h,
  cases h2,
  rw h_h,
  rw h2_h,
  have hw : h_w = 1 := sorry,
  have h2w : h2_w = 1 := sorry,
  rw hw,
  rw h2w,
  ring,
end


/- #4
Prove the following propositions. Remember that
throughout this file, each definition implicitly
includes β as a type and r as an arbitrary binary 
relation on β. In addition to formal proofs, give
an English language proof of the last of the three
problems.
-/

-- A
example : asymmetric r → irreflexive r :=
begin
  unfold asymmetric irreflexive,
  assume h k q,
  have h2:= h q,
  contradiction,
end

-- B
example : irreflexive r → transitive r → asymmetric r :=
begin
  unfold transitive asymmetric irreflexive,
  assume h q,
  assume x y,
  assume rxy,
  assume ryx,
  have rxx:= h x,
  have h2:= q rxy,
  have contr:= h2 ryx,
  contradiction,
 

end

-- C
/-
this is not provable
consider the transitive relation >. It is not symmetric since if a > b then b is not > a. 
It is irreflexive since a is not > a.
-/
example : transitive r → ¬ symmetric r → ¬ irreflexive r :=
begin
end


end relation
