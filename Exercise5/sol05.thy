(*<*)
theory sol05
imports "~~/src/HOL/IMP/Big_Step" "~~/src/HOL/IMP/Small_Step"
begin
(*>*)
text {* \ExerciseSheet{5}{11.~11.~2014, 11:11am} *}
text {* \Exercise{Program Equivalence}

Prove or disprove (by giving counterexamples) the following program equivalences.
\begin{enumerate}
\item
\mbox{@{term "IF And b1 b2 THEN c1 ELSE c2 \<sim> IF b1 THEN IF b2 THEN c1 ELSE c2 ELSE c2"}}
\item
@{term "WHILE And b1 b2 DO c \<sim> WHILE b1 DO WHILE b2 DO c"}
\item
@{term "WHILE And b1 b2 DO c \<sim> WHILE b1 DO c;; WHILE And b1 b2 DO c"}
\item
@{term "WHILE Or b1 b2 DO c \<sim> WHILE Or b1 b2 DO c;; WHILE b1 DO c"}
\end{enumerate}
*}

(*
a) equivalent, see below
b) not equivalent:  {a=2, b=1} while (a < 3 & b < 2) do a := 4
c) not equivalent:  {a=1}      while (a < 2 & a < 1) do a := 4
d) equivalent, see below
*)

text {* Hint: Use the following definition for @{text Or}: *}

definition Or :: "bexp \<Rightarrow> bexp \<Rightarrow> bexp" where
  "Or b1 b2 = Not (And (Not b1) (Not b2))"

(*<*)
lemma
  "IF And b1 b2 THEN c1 ELSE c2 \<sim> IF b1 THEN IF b2 THEN c1 ELSE c2 ELSE c2"
  (is "?i \<sim> ?ii")
proof -  (* sledgehammer also proves this, but here is a detailed proof *)
  {
    fix s t
    assume "(?i, s) \<Rightarrow> t"
    moreover
    {
      assume "bval b1 s \<and> bval b2 s"
      hence "bval (And b1 b2) s" by simp
    }
    moreover
    {
      assume "\<not>bval b1 s \<or> \<not>bval b2 s"
      hence "\<not>bval (And b1 b2) s" by simp
    }
    ultimately
    have "(?ii, s) \<Rightarrow> t" by blast
  }
  then show ?thesis by auto (* the other direction is automatic *)
qed

text {* At the end of a loop the condition is always false *}

lemma While_end: "(WHILE b DO c, s) \<Rightarrow> t \<Longrightarrow> \<not>bval b t"
proof(induction "WHILE b DO c" s t rule: big_step_induct)
  case WhileFalse thus ?case .
next
  case WhileTrue show ?case by fact
qed

(** Alternative proof **)
lemma "(WHILE b DO c, s) \<Rightarrow> t \<Longrightarrow> \<not>bval b t"
proof -
  assume "(WHILE b DO c, s) \<Rightarrow> t"
  then obtain c' where "(c', s) \<Rightarrow> t" and "c' = WHILE b DO c" by blast
  then show "\<not>bval b t"
    by (induct c' s t rule: big_step_induct) auto
qed

lemma "WHILE Or b1 b2 DO c \<sim> WHILE Or b1 b2 DO c;; WHILE b1 DO c"
proof -
  {
    fix s
    assume "\<not>bval (Or b1 b2) s"
    hence "\<not>bval b1 s" by (auto simp add: Or_def)
  }
  then show ?thesis by (blast intro!: While_end)
qed
(*>*)

(*<*)
end
(*>*)
