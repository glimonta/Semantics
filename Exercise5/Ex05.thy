theory Ex05
imports "~~/src/HOL/IMP/Big_Step" Main
begin

definition "Or b1 b2 \<equiv> Not (And (Not b1) (Not b2))"

term "op \<sim>"

lemma "IF (And b1 b2) THEN c1 ELSE c2
  \<sim> IF b1 THEN IF b2 THEN c1 ELSE c2 ELSE c2"
  (* usamos split_if cuando el if esta en la conclusión, si esta en las premisas usamos split_if_asm *)
  apply (auto split: split_if_asm) 
  apply (rule IfTrue)
  apply assumption
  apply (rule IfTrue)
  apply assumption
  apply assumption

  apply (rule IfTrue)
  apply assumption
  apply (rule IfFalse)
  apply assumption
  apply assumption

  apply (rule IfFalse)
  apply assumption
  apply assumption
  done
(*
lemma 
  defines "b1 \<equiv> Bc True" and "b2 \<equiv> Bc False" and "c \<equiv> SKIP"
  shows "\<not>(WHILE And b1 b2 DO c \<sim> WHILE b1 DO WHILE b2 DO c)"
  unfolding b1_def b2_def
  apply auto
  apply (rule exI[where x="<>"])
  apply (rule exI[where x="<>"])
  apply (auto)  

*)

lemma "\<not>(WHILE And b1 b2 DO c \<sim> WHILE b1 DO WHILE b2 DO c)"
proof 
  assume "WHILE And b1 b2 DO c \<sim> WHILE b1 DO WHILE b2 DO c"


end
