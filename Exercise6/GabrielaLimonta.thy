theory GabrielaLimonta
imports Main "~~/src/HOL/IMP/Big_Step" "~~/src/HOL/IMP/Small_Step" "~~/src/HOL/IMP/Compiler" "~~/src/HOL/IMP/Star"
begin

(* Homework 6.1 *)
fun whileFree :: "com \<Rightarrow> bool" where
  "whileFree SKIP = True"
| "whileFree (_ ::= _) = True"
| "whileFree (c1;;c2) = (whileFree c1 \<and> whileFree c2)"
| "whileFree (IF b THEN c1 ELSE c2) = (whileFree c1 \<and> whileFree c2)"
| "whileFree (WHILE b DO c) = False"

value "whileFree SKIP"
value "whileFree (x ::= (N 5))"
value "whileFree (SKIP;; x ::= (N 5))"
value "whileFree ((WHILE (Bc True) DO SKIP);; x ::= (N 5))"
value "whileFree (x ::= (N 5) ;; (WHILE (Bc True) DO SKIP))"
value "whileFree (IF (Bc True) THEN SKIP ELSE SKIP)"
value "whileFree (IF (Bc True) THEN SKIP ELSE (WHILE (Bc True) DO SKIP))"
value "whileFree (WHILE (Bc True) DO SKIP)"

(* For all commands c in which exist no while loop, the big step semantics yields a result state *)
lemma "(\<forall>c. (whileFree c)) \<Longrightarrow> (\<exists> t. (c,s) \<Rightarrow> t)"
proof (induction c arbitrary: s)
print_cases
case SKIP
  thus ?case by auto
next
case Assign
  thus ?case by auto
next
case Seq
  thus ?case by blast
next
case If
  thus ?case by blast
next
case While
  thus ?case using whileFree.simps(5) by auto
qed

(* For all commands c in which there is a state where big step semantics yields no result,
   c contains a while loop
 *)
lemma "(\<forall>c. \<not>(\<exists> t. (c,s) \<Rightarrow> t)) \<Longrightarrow> \<not>(whileFree c)"
proof (induction c arbitrary: s)
print_cases
case SKIP
  thus ?case by auto
next
case Assign
  thus ?case by auto
next
case Seq
  thus ?case by blast
next
case If
  thus ?case by blast
next
case While
  thus ?case using whileFree.simps(5) by auto
qed

(* Homework 6.2 *)

fun iexec_abs :: "instr \<Rightarrow> config \<Rightarrow> config" where
  "iexec_abs instr (i, s, stk) = (case instr of
    LOADI n \<Rightarrow> (i+1, s, n#stk) |
    LOAD x \<Rightarrow> (i+1, s, s x # stk) |
    ADD \<Rightarrow> (i+1, s, (hd2 stk + hd stk) # tl2 stk) |
    STORE x \<Rightarrow> (i+1, s(x := hd stk), tl stk) |
    JMP n \<Rightarrow> (n, s, stk) |
    JMPLESS n \<Rightarrow> (if hd2 stk < hd stk then n else i+1, s, tl2 stk) |
    JMPGE n \<Rightarrow> (if hd2 stk \<ge> hd stk then n else i+1, s, tl2 stk)
    )"

definition
  exec1_abs :: "instr list \<Rightarrow> config \<Rightarrow> config \<Rightarrow> bool"
    (" (_/ \<turnstile>\<^sub>a ( _ \<rightarrow>/ _))" [59,0,59] 60)
where
  "P \<turnstile>\<^sub>a c \<rightarrow> c' =
  (\<exists>i s stk. c = (i, s, stk) \<and> c' = iexec_abs(P!!i) (i, s, stk) \<and> 0 \<le> i \<and> i < size P)"

lemma exec1_absI [intro]:
  "\<lbrakk> c' = iexec_abs (P!!i) (i, s, stk); 0\<le>i; i < size P \<rbrakk> \<Longrightarrow> P \<turnstile>\<^sub>a (i, s, stk) \<rightarrow> c' "
by (metis exec1_abs_def)

abbreviation exec_abs :: "instr list \<Rightarrow> config \<Rightarrow> config \<Rightarrow> bool" (" (_/ \<turnstile>\<^sub>a (_ \<rightarrow>*/ _))" 50)
where
  "exec_abs P \<equiv> star (exec1_abs P)"


fun abs_to_rel :: "int \<Rightarrow> instr \<Rightarrow> instr" where
  "abs_to_rel i (LOADI n) = LOADI n" |
  "abs_to_rel i (LOAD x) = LOAD x" |
  "abs_to_rel i ADD = ADD" |
  "abs_to_rel i (STORE x) = STORE x" |
  "abs_to_rel i (JMP n) = JMP (n - i)" |
  "abs_to_rel i (JMPLESS n) = JMPLESS (n - i)" |
  "abs_to_rel i (JMPGE n) = JMPGE (n - i)"

fun index_map :: "(int \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> int \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "index_map f i [] = []"
| "index_map f i (x#xs) = f i x # index_map f (i+1) xs"

fun cnv_to_rel :: "instr list \<Rightarrow> instr list" where
  "cnv_to_rel is = index_map abs_to_rel 0 is"

lemma index_map_len[simp]: "size (index_map f i l) = size l"
apply (induction l arbitrary: i)
apply (auto)
done

lemma index_map_idx [simp]: "\<lbrakk>0\<le>i; i< size l \<rbrakk> \<Longrightarrow> index_map f k l !! i = f (i+k) (l!!i)"
apply (induction l arbitrary: i k)
apply (auto)
done

lemma "abs_to_rel 0 a = a"
apply (induction)
apply (auto)
done

lemma "P \<turnstile>\<^sub>a c \<rightarrow> c' \<longleftrightarrow> cnv_to_rel P \<turnstile> c \<rightarrow> c'"
proof
assume "P \<turnstile>\<^sub>a c \<rightarrow> c'"
show  "P \<turnstile>\<^sub>a c \<rightarrow> c' \<Longrightarrow> cnv_to_rel P \<turnstile> c \<rightarrow> c'"
proof (induction P arbitrary: c)
print_cases
  case Nil
  from this have "\<not>(\<exists> i s stk. c = (i, s, stk) \<and> c' = iexec_abs([]!!i) (i, s, stk) \<and> 0 \<le> i \<and> i < size [])" by simp
  then have "False" by (metis (full_types) Nil.prems exec1_abs_def list.size(3) not_less of_nat_0)
  then show ?case by auto
next
  case (Cons a P)
  thus ?case sorry
qed
next
assume a: "cnv_to_rel P \<turnstile> c \<rightarrow> c'"
show "cnv_to_rel P \<turnstile> c \<rightarrow> c' \<Longrightarrow> P \<turnstile>\<^sub>a c \<rightarrow> c'"
proof (induction P arbitrary: c)
print_cases
  case Nil 
    from this have "[] \<turnstile> c \<rightarrow> c'" using cnv_to_rel.simps[of "[]"] and index_map.simps(1)[of abs_to_rel 0] by auto
    then have "\<not>(\<exists>i s stk. c = (i,s,stk) \<and> c' = iexec([]!!i) (i,s,stk) \<and> 0 \<le> i \<and> i < size [])" by simp
    then have "False" by (metis `[] \<turnstile> c \<rightarrow> c'` exec1_def list.size(3) not_less of_nat_0)
    from this show ?case by auto
next
  case (Cons a P)
    from this and a have "(index_map abs_to_rel 0 (a#P)) \<turnstile> c \<rightarrow> c'" by auto
    then show ?case sorry
qed
qed


lemma "P \<turnstile>\<^sub>a c \<rightarrow>* c' \<longleftrightarrow> cnv_to_rel P \<turnstile> c \<rightarrow>* c'"
proof
assume "P \<turnstile>\<^sub>a c \<rightarrow>* c'"
show "P \<turnstile>\<^sub>a c \<rightarrow>* c' \<Longrightarrow> cnv_to_rel P \<turnstile> c \<rightarrow>* c'"
  proof (induction P arbitrary: c c')
  print_cases
  case Nil
    thus ?case sorry
  next
  case (Cons a P)
    thus ?case sorry
qed
next
assume "cnv_to_rel P \<turnstile> c \<rightarrow>* c'"
show "cnv_to_rel P \<turnstile> c \<rightarrow>* c' \<Longrightarrow> P \<turnstile>\<^sub>a c \<rightarrow>* c'"
  proof (induction P arbitrary: c c')
  print_cases
  case Nil
    from this show ?case sorry
  next
  case (Cons a P)
    thus ?case sorry
  qed
qed

end
