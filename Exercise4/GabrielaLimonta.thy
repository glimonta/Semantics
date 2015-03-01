theory GabrielaLimonta
imports Main
begin

(* Homework 4.1 *)
type_synonym ('q, 'l) lts = "'q \<Rightarrow> 'l \<Rightarrow> 'q \<Rightarrow> bool"

inductive word :: "('q, 'l) lts \<Rightarrow> 'q \<Rightarrow> 'l list \<Rightarrow> 'q \<Rightarrow> bool" for \<delta> where
  E: "word \<delta> u [] u" |
  NE: "\<lbrakk>\<delta> u w x ; word \<delta> x ws v\<rbrakk> \<Longrightarrow> word \<delta> u (w#ws) v"

definition "det \<delta>  \<equiv> \<forall> q a q1 q2. \<delta> q a q1 \<and> \<delta> q a q2 \<longrightarrow> q1 = q2"

inductive_cases empty_elim: "word \<delta> q [] q'"
inductive_simps empty_simp: "word \<delta> q [] q'"

lemma aux[simp]: "word \<delta> q [] q' \<longleftrightarrow> q=q'"
proof
  assume a: "word \<delta> q [] q'"
  thus "q = q'" using empty_elim empty_simp by (metis a)
next
  assume "q=q'"
  thus "word \<delta> q [] q'" using word.E by simp
qed

lemma
  assumes det: "det \<delta>"
  shows "word \<delta> q w q' \<Longrightarrow> word \<delta> q w q'' \<Longrightarrow> q' = q''"
  proof (induction rule: word.induct)
  print_cases
  case E show ?case using E by auto
next
  case (NE u w x ws v)
  show ?case using assms NE aux
  using [[simp_trace]]
sorry
qed

(* Homework 4.2 *)
datatype ab = a | b

inductive_set S :: "ab list set" where
  left: "w1 \<in> S \<Longrightarrow> w2 \<in> S \<Longrightarrow> [a] @ w1 @ [b] @ w2 \<in> S"
| nil: "[] \<in> S"

inductive_set T :: "ab list set" where
  right: "w1 \<in> T \<Longrightarrow> w2 \<in> T \<Longrightarrow> w1 @ [a] @ w2 @ [b] \<in> T"
| nil: "[] \<in> T"


lemma S_SS[simp]: 
  assumes "w1 \<in> S"
  assumes "w2 \<in> S"
  shows "w1 @ w2 \<in> S"
using assms
proof (induction rule: S.induct)
print_cases
  case nil show ?case using nil.prems S.left S.nil by simp
next
  case (left w1 w2)
  show ?case using S.left left append_assoc append_Cons append_Nil by auto
qed

lemma T_TT[simp]: 
  assumes "w1 \<in> T"
  assumes "w2 \<in> T"
  shows "w2 @ w1 \<in> T"
using assms
proof (induction rule: T.induct)
print_cases
  case nil show ?case using nil.prems T.right T.nil by simp
next
  case (right w1 w2)
  show ?case using right append_assoc append_Cons append_Nil by (metis T.right)
qed


lemma S_imp_T:
  assumes w: "w \<in> S"
  shows "w \<in> T"
  using assms
proof (induction rule: S.induct)
print_cases
  case nil show ?case using T.nil by simp
next
  case (left w1 w2)
  show ?case
  using left T.intros append_assoc append_Cons append_Nil T_TT
  by (metis Tp_T_eq)
qed

lemma T_imp_S:
  assumes w: "w \<in> T"
  shows "w \<in> S"
using assms
proof (induction rule: T.induct)
print_cases
  case nil show ?case using S.nil by simp
next
  case (right w1 w2)
  show ?case
  using right S.intros append_assoc append_Cons append_Nil S_SS by simp
qed

lemma "S = T"
proof
  show "S \<subseteq> T"
  using S_imp_T by auto
next
  show "T \<subseteq> S"
  using T_imp_S by auto
qed
  
end
