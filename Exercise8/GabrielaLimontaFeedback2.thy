theory GabrielaLimonta2
imports "~~/src/HOL/IMP/Big_Step"
begin

(** Score: 2/5
*)

(* Homework 8.2 *)

(* True if command doesn't change value of a variable *)
fun invar :: "vname \<Rightarrow> com \<Rightarrow> bool" where
  "invar x SKIP = True" |
  "invar x (y ::= a) = (x = y)" |
  "invar x (c1;;c2) = (invar x c1 \<and> invar x c2)" |
  "invar x (IF b THEN c1 ELSE c2) = (invar x c1 \<and> invar x c2)" |
  "invar x (WHILE b DO c) = invar x c"

(* True if command increments value of a variable *)
fun incr :: "vname \<Rightarrow> com \<Rightarrow> bool" where
  "incr x SKIP = False" |
  "incr x (y ::= a) = (if x = y then (
    case a of
      (Plus (V z) (N n)) \<Rightarrow> (if (x = z \<and> n > 0) then True else False) |
      _ \<Rightarrow> False )
    else False)" |
  "incr x (c1;;c2) = ((incr x c1 \<and> incr x c2) \<or> (incr x c1 \<and> invar x c2) \<or> (invar x c1 \<and> incr x c2))" |
  "incr x (IF b THEN c1 ELSE c2) = (incr x c1 \<and> incr x c2)" |
  "incr x (WHILE b DO c) = False"

(*
abbreviation "x \<equiv> ''x''" abbreviation "y \<equiv> ''y''"
abbreviation "L \<equiv> (WHILE (Less (V y) (N 2)) DO y ::= Plus (V y) (N 1))"
abbreviation "I n \<equiv> x ::= Plus (V x) (N n)"
value "incr x (I 1;;I 2)" value "incr x (I 1 ;; L)"
value "incr x (L ;; I 1)" value "incr x (IF (Less (V y) (N 1)) THEN I 1 ELSE I 2)"

value "incr x (I -1;;I 2)" value "incr x (x ::= V x;; I 1)"
*)

(** You are missing an aux-lemma about invar here!**)

lemma incr: "(c, s) \<Rightarrow> t \<Longrightarrow> incr x c \<Longrightarrow> s x < t x"
proof (induction rule: big_step_induct)
print_cases
  case Skip
    thus ?case by auto
  next
  case (Assign y a)
    thus ?case sorry
  next
  case (Seq c\<^sub>1 s\<^sub>1 s\<^sub>2 c\<^sub>2 s\<^sub>3)
    thus ?case sorry
  next
  case (IfTrue b s c\<^sub>1 t c\<^sub>2)
    thus ?case by auto
  next
  case (IfFalse b s c\<^sub>2 t c\<^sub>1)
    thus ?case by auto
  next
  case (WhileTrue b s\<^sub>1 c s\<^sub>2 s\<^sub>3)
    thus ?case by auto
  next
  case (WhileFalse b s c)
    thus ?case by auto
qed

lemma int_less_induct:
  assumes "\<And>i. i \<ge> k \<Longrightarrow> P i" and "\<And>i. i < k \<Longrightarrow> (\<And>j. i < j \<Longrightarrow> P j) \<Longrightarrow> P i"
  shows "P(i::int)"
  apply(induction "nat(k-i)" arbitrary: i rule: nat_less_induct)
  apply(case_tac "k \<le> i")
  apply(simp add: assms(1))
by(metis (full_types) assms(2) diff_self diff_strict_left_mono not_le zless_nat_conj)

inductive "term" :: "com \<Rightarrow> bool" where
  Skip: "term SKIP" |
  Assign: "term (x::=a)" |
  Seq: "\<lbrakk> term c1; term c2 \<rbrakk> \<Longrightarrow> term (c1;;c2)" |
  If: "\<lbrakk> term c1; term c2 \<rbrakk> \<Longrightarrow> term (IF b THEN c1 ELSE c2)" |
  While: "\<lbrakk> b = (Less (V x) (N n)); incr x c \<rbrakk> \<Longrightarrow> term (WHILE b DO c)"
(** You do not exclude the case that c has a non-terminating inner loop, like
  in while (x>0) {x--; while (true) skip; }
*)

lemma term_w: assumes "\<And>s. EX t. (c, s) \<Rightarrow>t" "incr x c"
  shows "EX t. (WHILE Less (V x) (N k) DO c, s) \<Rightarrow> t"
proof (induction "s x" arbitrary: s rule: int_less_induct[of k])
print_cases
  case 1
    thus ?case by fastforce
  next
  case 2
    thus ?case using WhileFalse and WhileTrue and assms and incr by metis
qed

theorem "term c \<Longrightarrow> EX t. (c, s) \<Rightarrow> t"
proof (induction arbitrary: s rule: term.induct)
print_cases
  case Skip
    thus ?case by auto
  next
  case Assign
    thus ?case by auto
  next
  case (Seq c1 c2)
    from this and term.Seq[of c1 c2] obtain s1 where "(c1, s) \<Rightarrow> s1" and "term (c1;;c2)" by auto
    moreover from this and Seq obtain s2 where "(c2, s1) \<Rightarrow> s2" by auto
    ultimately show ?case by auto
(*
  big_step :: "com \<times> state \<Rightarrow> state \<Rightarrow> bool" (infix "\<Rightarrow>" 55)
where
Skip: "(SKIP,s) \<Rightarrow> s" |
Assign: "(x ::= a,s) \<Rightarrow> s(x := aval a s)" |
Seq: "\<lbrakk> (c\<^sub>1,s\<^sub>1) \<Rightarrow> s\<^sub>2;  (c\<^sub>2,s\<^sub>2) \<Rightarrow> s\<^sub>3 \<rbrakk> \<Longrightarrow> (c\<^sub>1;;c\<^sub>2, s\<^sub>1) \<Rightarrow> s\<^sub>3" |
IfTrue: "\<lbrakk> bval b s;  (c\<^sub>1,s) \<Rightarrow> t \<rbrakk> \<Longrightarrow> (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<Rightarrow> t" |
IfFalse: "\<lbrakk> \<not>bval b s;  (c\<^sub>2,s) \<Rightarrow> t \<rbrakk> \<Longrightarrow> (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<Rightarrow> t" |
WhileFalse: "\<not>bval b s \<Longrightarrow> (WHILE b DO c,s) \<Rightarrow> s" |
WhileTrue:
"\<lbrakk> bval b s\<^sub>1;  (c,s\<^sub>1) \<Rightarrow> s\<^sub>2;  (WHILE b DO c, s\<^sub>2) \<Rightarrow> s\<^sub>3 \<rbrakk> 
\<Longrightarrow> (WHILE b DO c, s\<^sub>1) \<Rightarrow> s\<^sub>3" *)
  next
  case (If c1 c2)
    from this obtain s' where "(c1, s) \<Rightarrow> s'" by auto
    moreover from If obtain s'' where "(c2, s) \<Rightarrow> s''" by auto
    ultimately show ?case by auto
  next
  case (While b x n c)
    from this and term_w[of c x n s] show ?case sorry
qed

end
