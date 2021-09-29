-- 1
example : 0 ≠ 1 :=
begin
  -- ¬ (0 = 1)
  -- (0 = 1) → false
  assume h,
  cases h,
end


-- 2
example : 0 ≠ 0 → 2 = 3 :=
begin
  assume h,
  have f : false := h (eq.refl 0),
  exact false.elim (f),
end

-- 3
example : ∀ (P : Prop), P → ¬¬P :=
begin
  assume P,
  assume (p : P),
  -- ¬¬P
  -- ¬P → false
  -- (P → false) → false
  assume h,
  have f := h p,
  exact f,
end 

-- We might need classical (vs constructive) reasoning 
#check classical.em
open classical
#check em

/-
axiom em : ∀ (p : Prop), p ∨ ¬p

This is the famous and historically controversial
"law" (now axiom) of the excluded middle. It's is
a key to proving many intuitive theorems in logic
and mathematics. But it also leads to giving up on
having evidence *why* something is either true or
not true, in that you no longer need a proof of 
either P or of ¬P to have a proof of P ∨ ¬P.
-/

-- 4
theorem neg_elim : ∀ (P : Prop), ¬¬P → P :=
begin
  assume P,
  assume h,
  have pornp := classical.em P,
  cases pornp with p pn,
  assumption,
  contradiction,
end

-- 5
theorem demorgan_1 : ∀ (P Q : Prop), ¬ (P ∧ Q) ↔ ¬ P ∨ ¬ Q :=
begin
  assume P Q,
  apply iff.intro,
  -- forward
  assume h,
  cases (em P) with p np,
  cases em Q with q nq,
  have pandq := and.intro p q,
  have f := h pandq,
  exact false.elim f,
  apply or.intro_right,
  exact nq,
  apply or.intro_left,
  exact np,
   -- backward
  assume h,
  cases h with np nq,
  assume pandq,
  have P := and.elim_left pandq,
  exact np P,
  assume pandq,
  have Q := and.elim_right pandq,
  exact nq Q,
end


-- 6
theorem demorgan_2 : ∀ (P Q : Prop), ¬ (P ∨ Q) → ¬P ∧ ¬Q :=
begin
  assume P Q,
  assume h,
  cases (em P) with p np,
  cases em Q with q nq,
  have porq := or.intro_left Q p,
  have f := h porq,
  exact false.elim f,
  have porq := or.intro_left Q p,
  have f := h porq,
  exact false.elim f,
  apply and.intro,
  exact np,
  cases em Q with q nq,
  have qorp := or.intro_left P q,
  have porq := or.symm qorp,
  have f := h porq,
  exact false.elim f,
  exact nq,
end


-- 7
theorem disappearing_opposite : 
  ∀ (P Q : Prop), P ∨ ¬P ∧ Q ↔ P ∨ Q := 
begin
  assume P Q,
  apply iff.intro,
  -- forward
  assume h,
  apply or.elim h,
  assume P,
  apply or.intro_left,
  exact P,
  assume h,
  have Q := and.elim_right h,
  apply or.intro_right,
  exact Q,
  -- backward
  assume h,
  cases (em P) with p np,
  cases em Q with q nq,
  apply or.intro_left,
  exact p,
  apply or.intro_left,
  exact p,
  cases em Q with q nq,
  have npandq := and.intro np q,
  apply or.intro_right,
  exact npandq,
  apply or.elim h,
  assume p,
  apply or.intro_left,
  exact p,
  assume q,
  have npandq := and.intro np q,
  apply or.intro_right,
  exact npandq,
end


-- 8
theorem distrib_and_or : 
  ∀ (P Q R: Prop), (P ∨ Q) ∧ (P ∨ R) ↔
                    P ∨ (Q ∧ R) :=
begin
  assume P Q R,
  apply iff.intro,
  -- forward
  assume h,
  have porq := and.elim_left h,
  apply or.intro_left,
  cases em P with p np,
  exact p,
  


end

-- remember or is right associative
-- you need this to know what the lefts and rights are
-- 9
theorem distrib_and_or_foil : 
  ∀ (P Q R S : Prop),
  (P ∨ Q) ∧ (R ∨ S) ↔
  (P ∧ R) ∨ (P ∧ S) ∨ (Q ∧ R) ∨ (Q ∧ S) :=
begin
  assume P Q R S,
  apply iff.intro,
  -- forward
  assume h,


end


/- 10
Formally state and prove the proposition that
not every natural number is equal to zero.
-/
lemma not_all_nats_are_zero : ∃ (n : ℕ), n ≠ 0:=
begin
  apply exists.intro 1 _,
  assume h,
  cases h,
end 

-- 11. equivalence of P→Q and (¬P∨Q)
example : ∀ (P Q : Prop), (P → Q) ↔ (¬P ∨ Q) :=
begin
  assume P Q,
  apply iff.intro,
  -- forward
  assume h,
  cases em P with p np,
  have q := h p,
  apply or.intro_right,
  exact q,
  apply or.intro_left,
  exact np,
  -- backward
  assume h,
  assume p,
  apply or.elim h,
  assume np,
  have f := np p,
  exact false.elim f,
  assume q,
  exact q,
end

-- 12
example : ∀ (P Q : Prop), (P → Q) → (¬ Q → ¬ P) :=
begin
  assume P Q,
  assume h,
  cases em P with p np,
  assume nq,
  have q := h p,
  have f := nq q,
  exact false.elim f,
  assume nq,
  exact np,
end

-- 13
example : ∀ (P Q : Prop), ( ¬P → ¬Q) → (Q → P) :=
begin
  assume P Q,
  assume h,
  cases em P with p np,
  assume q,
  exact p,
  have nq := h np,
  assume q,
  have f := nq q,
  exact false.elim f,
end

