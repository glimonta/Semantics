theory tmpl03_ab
  imports Main
begin

datatype ab = a | b

inductive_set S :: "ab list set" where
  "w \<in> S \<Longrightarrow> [a] @ w \<in> S"
| "w \<in> S \<Longrightarrow> w @ [b] \<in> S"
| "[] \<in> S"

fun is_ab :: "ab list \<Rightarrow> bool" where
  "is_ab [] = undefined" 
| "is_ab (x#xs) = undefined" 

lemma "w \<in> S \<Longrightarrow> is_ab w"
  oops

end
