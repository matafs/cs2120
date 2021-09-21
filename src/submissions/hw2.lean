/-
Prove the following simple logical conjectures.
Give a formal and an English proof of each one.
Your English language proofs should be complete
in the sense that they identify all the axioms
and/or theorems that you use.
-/

example : true := true.intro

-- example : false :=     -- trick question? why? there is no proof of false

example : ∀ (P : Prop), P ∨ P ↔ P := 
begin
  assume P,
  apply iff.intro _ _,
  -- forward
  assume porp,
  apply or.elim porp,
  assume p,
  exact p,
  assume p,
  exact p,
  -- backward
  assume p,
  exact or.intro_left P p,
end

example : ∀ (P : Prop), P ∧ P ↔ P := 
begin
  assume P,
  apply iff.intro _ _,
  -- forward
    assume pp,
    exact and.elim_left pp,
  -- backward
    assume p,
    apply and.intro,
    exact p,
    exact p,
end

example : ∀ (P Q : Prop), P ∨ Q ↔ Q ∨ P := 
begin
  assume P Q,
  apply iff.intro _ _,
  -- forward
  assume porq,
  apply or.symm,
  exact porq,
  -- backward
  assume qorp,
  apply or.symm,
  exact qorp,
end

example : ∀ (P Q : Prop), P ∧ Q ↔ Q ∧ P := 
begin
  assume P Q,
  apply iff.intro,
  -- forward
  assume pandq,
  apply and.symm,
  exact pandq,
  -- forward
  assume qandp,
  apply and.symm,
  exact qandp,
end

example : ∀ (P Q R : Prop), P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := 
begin
  assume P Q R,
  apply iff.intro,
  -- forward
  assume h,
  have qorr : Q ∨ R := and.elim_right h,
  have p : P := and.elim_left h,
  apply or.elim qorr,
  assume q,
  apply or.intro_left,
  apply and.intro,
  exact p,
  exact q,
  assume r,
  apply or.intro_right,
  apply and.intro,
  exact p,
  exact r,
  -- backward
  assume h,
  apply or.elim h,
  assume pandq,
  apply and.intro,
  exact and.elim_left pandq,
  apply or.intro_left,
  exact and.elim_right pandq,
  assume pandr,
  apply and.intro,
  exact and.elim_left pandr,
  apply or.intro_right,
  exact and.elim_right pandr,
end

example : ∀ (P Q R : Prop), P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := 
begin
  assume P Q R,
  apply iff.intro,
  -- forward
  assume h,
  apply and.intro,
  apply or.elim h,
  assume P,
  apply or.intro_left,
  exact P,
  assume QandR,
  apply or.intro_right,
  exact and.elim_left QandR,
  apply or.elim h,
  assume P,
  apply or.intro_left,
  exact P,
  assume QandR,
  apply or.intro_right,
  exact and.elim_right QandR,
  -- backward
  assume h,
  apply and.elim h,
  assume porq,
  apply or.elim porq,
  assume P,
  assume porr,
  apply or.intro_left,
  exact P,
  assume Q,
  assume porr,
  apply or.elim porr,
  assume P,
  apply or.intro_left,
  exact P,
  assume R,
  apply or.intro_right,
  apply and.intro,
  exact Q,
  exact R,
end

example : ∀ (P Q : Prop), P ∧ (P ∨ Q) ↔ P := 
begin
  assume P Q,
  apply iff.intro,
  -- forward
  assume h,
  exact and.elim_left h,
  -- backward
  assume P,
  apply and.intro,
  exact P,
  apply or.intro_left,
  exact P,
end

example : ∀ (P Q : Prop), P ∨ (P ∧ Q) ↔ P := 
begin
  assume P Q,
  apply iff.intro,
  assume h,
  --forward
  apply or.elim h,
  assume P,
  exact P,
  assume pandq,
  exact and.elim_left pandq,
  -- backward
  assume P,
  apply or.intro_left,
  exact P,
end

example : ∀ (P : Prop), P ∨ true ↔ true := 
begin
  assume P,
  apply iff.intro,
  -- forward
  assume h,
  apply or.elim h,
  assume P,
  exact true.intro,
  assume t,
  exact true.intro,
  -- backward
  assume t,
  apply or.intro_right,
  exact true.intro,
end

example : ∀ (P : Prop), P ∨ false ↔ P := 
begin
  assume P,
  apply iff.intro,
  -- forward
  assume h,
  apply or.elim h,
  assume P,
  exact P,
  assume f,
  exact false.elim f,
  -- backward
  assume P,
  apply or.intro_left,
  exact P,
end

example : ∀ (P : Prop), P ∧ true ↔ P := 
begin
  assume P,
  apply iff.intro,
  -- forward
  assume h,
  exact and.elim_left h,
  -- backward
  assume P,
  apply and.intro,
  exact P,
  exact true.intro,
end

example : ∀ (P : Prop), P ∧ false ↔ false := 
begin
  assume P,
  apply iff.intro,
  -- forward
  assume h,
  exact and.elim_right h,
  -- backward
  assume f,
  apply and.intro,
  exact false.elim f,
  exact f,
end


