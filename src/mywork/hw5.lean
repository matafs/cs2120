import data.set

/-
CS2120 F21 HW5

The goals of this assignment are to give you
practice with proofs of propositions that use
existential quantificaton, and to develop your
understanding of formal and informal proofs in
set theory.
-/

/-
PART I: EXISTENTIAL QUANTIFICATION.
-/

/-
To start, suppose that α and β are arbitrary
types, and p and q are predicates on values
of these types: α and β, respectively.
-/

axioms 
  (α β : Type)    -- data types
  (p : α → Prop)  -- predicates
  (q : β → Prop)

/-
In this context complete the following tasks:

(1) Write a fluent English-language statement
of the proposition to be proved. 

(2) Provide a formal proof of the proposition.

(3) Write an informal proof of the proposition.
-/

-- here's the proposition
example : 
  (∃ (f : α → β), ∀ (a : α), p a → q (f a)) →
  (∃ (a : α), p a) → 
  (∃ (b : β), q b) := 

/-
What does this propositon say? Explain it in
plain English. Here's a start: "If there's a 
function that maps/takes every α value that ... 
-- your completed English rendition here:

There exists a function that takes every α value (such that for all a of type α, 
if a has property p then q is true) and returns a β value implies if there 
exists a of type α such that a has property p, then there exists b of type β
such that b has property q.
-/


-- Give your formal proof here
begin
  assume h,
  assume f,
  apply exists.elim f,
  assume a Pa,
  apply exists.elim h,
  assume atob fpaq,
  have paq := fpaq a,
  have Q := paq Pa,
  have b := atob a,
  apply exists.intro b,
  
end
  
/-
informal proof:
Assume α implies β for all α such that if α has property p then q is true.
Assume there exists a of type α with property p. Since a implies β and a implies 
q is true then there is a case where β has property q. Therfore if there exists a 
of type α with property p then there exists b of type β with property q. 
-/
