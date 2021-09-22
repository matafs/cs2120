theorem no_contradiction: ∀ (P : Prop), ¬(P ∧ ¬P) :=
begin
  assume P,
  assume h,
  have p : P := and.elim_left h,
  have notp : ¬P := and.elim_right h,
  apply notp p,
end

axiom excluded_middle : ∀ (P : Prop), (P ∨ ¬P)