axioms (P Q : Prop)

def if_P_then_Q : Prop := P → Q

-- assume P is true
-- assume we have a proof of P (p)
axiom p : P

-- assume we have a proof, pq, of P → Q
axiom pq : P → Q

-- intro for implies: assume premise, show conclusion
-- elimination rule for implies: appyly P → Q to P to get Q

#check pq
#check p
#check (pq p)

-- FORALL
namespace all

axioms 
  (T : Type)
  (P : T → Prop)
  (t : T)
  (a : ∀ (x : T), P x)
-- 
example: P t := a t

end all

-- AND & → 

axioms (A B : Prop)

