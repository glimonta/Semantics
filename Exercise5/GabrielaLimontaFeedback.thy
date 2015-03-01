(** Score: 8/10
  Unfortunately, left a sorry in a quite straightforward case ...

**)
theory GabrielaLimonta
imports Main "~~/src/HOL/IMP/Big_Step"
begin                             

fun exec :: "com \<Rightarrow> state \<Rightarrow> nat \<Rightarrow> state option" where
  "exec _ s 0 = None" 
| "exec SKIP s (Suc f) = Some s" 
| "exec (x::=v) s (Suc f) = Some (s(x:=aval v s))" 
| "exec (c1;;c2) s (Suc f) = (
    case (exec c1 s f) of None \<Rightarrow> None | Some s' \<Rightarrow> exec c2 s' f)" 
| "exec (IF b THEN c1 ELSE c2) s (Suc f) = 
    (if bval b s then exec c1 s f else exec c2 s f)" 
| "exec (WHILE b DO c) s (Suc f) = (
    if bval b s then 
      (case (exec c s f) of 
        None \<Rightarrow> None | 
        Some s' \<Rightarrow> exec (WHILE b DO c) s' f) 
    else Some s)"


text {* The two directions are proved separately. The proof of the first 
  direction should be quite straightforward, and is left to you. *}
lemma exec_imp_bigstep: "exec c s f = Some s' \<Longrightarrow> (c,s) \<Rightarrow> s'"
proof (induction arbitrary: s' rule: exec.induct[case_names None SKIP ASS SEMI IF WHILE])
print_cases
case (None uu sa)
  from this have False by auto
  thus ?case by blast
next
case (SKIP sa f)
  from this have "sa = s'" by auto
  thus ?case using `sa = s'` by auto
next
case (ASS x v sa f)
  from this have "s' = sa(x := aval v sa)" by auto
  thus ?case by blast
next 
case (SEMI c1 c2 sa f)
  thus ?case by (auto split: option.split_asm)
next
case (IF b c1 c2 sa f)
  thus ?case by (metis IfFalse IfTrue exec.simps(5))
next
case (WHILE b c sa f) 
  thus ?case
  (** Why give up on such a simple proof?
    When applying auto, you find unsplit if and unsplit option-case.
    So just add the split-rules ... and you are done!
  **)
  by (auto split: split_if_asm option.splits)
  (**sorry**)
qed


lemma exec_mono: "exec c s f = Some s' \<Longrightarrow> exec c s (f+k) = Some s'"
proof (induction c s f arbitrary: s'
    rule: exec.induct[case_names None SKIP ASS SEMI IF WHILE])
print_cases
case (None uu s s')
  from this have False by simp
  thus ?case by blast
next
case (SKIP s f s')
  from this have "s' = s" by simp
  thus ?case by auto
next
case (ASS x v s f s')
  from this have "s' = s(x := aval v s)" by simp
  thus ?case by auto
next
case (SEMI c1 c2 s f)
  thus ?case by (auto split: option.split option.split_asm)
next
case (IF b c1 c2 s f s')
  thus ?case by auto
next
case (WHILE b c s i s')
  thus ?case by (auto split: option.split_asm)
qed

lemma bigstep_imp_si:
  "(c,s) \<Rightarrow> s' \<Longrightarrow> \<exists>k. exec c s k = Some s'"
proof (induct rule: big_step_induct)
print_cases
  case (Skip s) have "exec SKIP s 1 = Some s" by auto
  thus ?case by blast
next
  case (WhileTrue b s1 c s2 s3)
  then obtain f1 f2 where "exec c s1 f1 = Some s2" 
    and "exec (WHILE b DO c) s2 f2 = Some s3" by auto
  with exec_mono[of c s1 f1 s2 f2] 
    exec_mono[of "WHILE b DO c" s2 f2 s3 f1] have 
    "exec c s1 (f1+f2) = Some s2" 
    and "exec (WHILE b DO c) s2 (f2+f1) = Some s3"
    by auto
  hence "exec (WHILE b DO c) s1 (Suc (f1+f2)) = Some s3" 
    using `bval b s1` by (auto simp add: add_ac)
  thus ?case by blast
next
  case (Seq c1 s1 s2 c2 s3)
  then obtain f1 f2 where "exec c1 s1 f1 = Some s2" and "exec c2 s2 f2 = Some s3"
    by auto
  with exec_mono[of c1 s1 f1 s2 f2] 
    exec_mono[of c2 s2 f2 s3 f1] 
  have 
    "exec c1 s1 (f1+f2) = Some s2" and "exec c2 s2 (f2+f1) = Some s3"
    by auto
  hence "exec (c1;;c2) s1 (Suc (f1+f2)) = Some s3" by (auto simp add: add_ac)
  thus ?case by blast
next
  case (Assign x a s)
  have "exec (x::=a) s (Suc 0) = Some (s(x := aval a s))" by auto
  thus ?case by blast
next
  case (IfTrue b s c1 t c2)
  then obtain f where "exec c1 s f = Some t" by auto
  from this and `bval b s` and `(c1, s) \<Rightarrow> t`
  have "exec (IF b THEN c1 ELSE c2) s (Suc f) = Some t" by auto
  thus ?case by blast
next
  case (IfFalse b s c2 t c1)
  then obtain f where "exec c2 s f = Some t" by auto
  from this and `\<not>bval b s` and `(c2, s) \<Rightarrow> t`
  have "exec (IF b THEN c1 ELSE c2) s (Suc f) = Some t" by auto
  thus ?case by blast
next
  case (WhileFalse b s c)
  from this have "exec (WHILE b DO c) s (Suc 0) = Some s" by auto
  thus ?case by blast
qed

text {* Finally, prove the main theorem of the homework: *}
theorem exec_equiv_bigstep: "(\<exists>k. exec c s k = Some s') \<longleftrightarrow> (c,s) \<Rightarrow> s'"
  proof 
  assume "\<exists>k. exec c s k = Some s'"
  then obtain f where "exec c s f = Some s'" by auto
  thus "(c,s) \<Rightarrow> s'" using exec_imp_bigstep[of c s f] by auto
next
  assume "(c,s) \<Rightarrow> s'"
  then show "\<exists>k. exec c s k = Some s'" using bigstep_imp_si[of c s s'] by auto
qed

end
