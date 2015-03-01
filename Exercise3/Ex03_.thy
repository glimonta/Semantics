theory Ex03_
imports Main "~~/src/HOL/IMP/AExp"
begin

inductive is_aval :: "aexp \<Rightarrow> state \<Rightarrow> val \<Rightarrow> bool" where
  N: "is_aval (N n) s n"
| V: "is_aval (V x) s (s x)"
| P: "\<lbrakk> is_aval a1 s v1; is_aval a2 s v2 \<rbrakk> \<Longrightarrow> is_aval (Plus a1 a2) s (v1 + v2)"

lemma "is_aval (Plus (N 2) (Plus (V x) (N 3))) s (2 + (s x + 3))"
  apply(rule is_aval.intros)+
  done

lemma aval1: "is_aval a s v \<Longrightarrow> aval a s = v"
  apply(induction a)
  apply()


end
