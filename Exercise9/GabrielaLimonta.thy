theory GabrielaLimonta
imports "~~/src/HOL/IMP/Big_Step" "~~/src/HOL/IMP/Vars"
begin

fun gen :: "com \<Rightarrow> (vname * aexp) set"
and "kill" :: "com \<Rightarrow> (vname * aexp) set" where
"gen SKIP = {}" |
"gen (x ::= a) = (if x \<notin> vars a then {(x, a)} else {})" |
"gen (c1 ;; c2) = (gen c1 - kill c2) \<union> gen c2" |
"gen (IF b THEN c1 ELSE c2) = (gen c1 - kill c2) \<inter> gen c2" |
"gen (WHILE b DO c) = gen c" |
"kill SKIP = {}" |
"kill (x ::= a) = {(y,e). y = x \<and> e \<noteq> a} \<union> {(y,e). x \<in> vars e}" |
"kill (c1 ;; c2) = kill c1 \<union> kill c2" |
"kill (IF b THEN c1 ELSE c2) = kill c1 \<union> kill c2" |
"kill (WHILE b DO c) = kill c"


definition AD :: "(vname * aexp) set \<Rightarrow> com \<Rightarrow> (vname * aexp) set" where
"AD A c = gen c \<union> (A - kill c)"

lemma "{(''x'', (N 5)), (''y'', (N 8))} = AD {(''x'', (N 4)), (''y'', (N 8))} (''x'' ::= (N 5))"
by (auto simp: AD_def)

theorem "\<lbrakk> (c,s) \<Rightarrow> s'; \<forall> (x, a) \<in> A. s x = aval a s \<rbrakk>
  \<Longrightarrow> \<forall> (x, a) \<in> AD A c. s' x = aval a s'"
proof (induction arbitrary: A rule: big_step_induct)
print_cases
case (Skip s)
  thus ?case using AD_def by auto
next
case (Assign x' a' s)
  thus ?case using AD_def by (auto split: if_splits)
next
case (Seq c1 s1 s2 c2 s3) 
  thus ?case using AD_def sorry
next
case (IfTrue b s c1 t)
  thus ?case using AD_def by auto
next
case (IfFalse b s c2 t)
  thus ?case using AD_def by auto
next
case (WhileFalse b s)
  thus ?case using AD_def and big_step.intros sorry
next
case (WhileTrue b s1 c s2 s3)
  thus ?case using AD_def and big_step.intros sorry
qed 

end
