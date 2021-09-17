/-
Theorom: Equality is symmetric
-/

theorem eq_symm :
∀ (T : Type) (x y : T), x = y → y = x := 
begin
  assume (T : Type), 
  assume (x y : T),
  assume (e : x = y),
  rw e, 
end
/- 
Theorom : Equality is symmetric
Proof:
Assume T is of any type and x and y are of type T. Given that x = y, using 
the substitutability of equality axiom y = x can be writen as y = y. 
Therefore, if x = y then y = x.
QED
 -/

 /-
 Theorom : Equality is transitive
 -/

 theorem equ_trans:
 ∀ (T : Type) (x y z: T), x = y → y = z → x = z :=
 begin
   assume (T : Type), 
   assume (x y z: T),
   assume (e1 : x = y),
   assume (e2 : y = z),
   rw e1,
   exact e2,
 end