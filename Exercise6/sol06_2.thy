(*<*)
theory sol06_2
imports "~~/src/HOL/IMP/Small_Step" "~~/src/HOL/IMP/Compiler"
begin
(*>*)
text {* \ExerciseSheet{6}{18.~11.~2014} 
*}

text {* 
\Exercise{Deskip}

Define a recursive function
*}
(*<*)(*kill*)
definition
"deskseq c1 c2 = (if c1=SKIP then c2 else if c2=SKIP then c1 else c1;;c2)"

definition
"deskif b c1 c2 =
 (if c1=SKIP & c2=SKIP then SKIP else IF b THEN c1 ELSE c2)"
(*>*)
fun deskip :: "com \<Rightarrow> com" (*<*)(*keep*)where(*>*)
(*<*)
"deskip (c1;;c2) = deskseq (deskip c1) (deskip c2)" |
"deskip (IF b THEN c1 ELSE c2) = deskif b (deskip c1) (deskip c2)" |
"deskip (WHILE b DO c) = WHILE b DO deskip c" |
"deskip c = c"
(*>*)

text{*
that eliminates as many @{const SKIP}s as possible from a command. For example:
@{prop[display]"deskip (SKIP;; WHILE b DO (x::=a;; SKIP)) = WHILE b DO x::=a"}
Prove its correctness by induction on @{text c}: *}

lemma "deskip c \<sim> c"
(*<*)
proof(induction c)
  case (Seq c1 c2)
  thus ?case
    by (auto simp add: deskseq_def) (metis Skip Big_Step.SkipE big_step.Seq)+
next
  case (If b c1 c2)
  thus ?case
    by (auto simp add: deskif_def) (metis big_step.IfFalse big_step.IfTrue Skip)
next
  case While thus ?case by (simp add: sim_while_cong)
qed auto
(*>*)

text{*
Remember lemma @{thm[source]sim_while_cong} for the @{text WHILE} case.
*}

(*<*)
end
(*>*)
