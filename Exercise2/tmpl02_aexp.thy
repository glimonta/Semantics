theory tmpl02_aexp
  imports Main
begin

type_synonym vname = string
type_synonym state = "string \<Rightarrow> int"
type_synonym val = "int"

declare algebra_simps[simp]

datatype aexp = N int | V vname | Plus aexp aexp | Mult int aexp

fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
"aval (N n) s = n" |
"aval (V x) s = s x" |
"aval (Plus a\<^sub>1 a\<^sub>2) s = aval a\<^sub>1 s + aval a\<^sub>2 s" |
"aval (Mult i a) s = i * aval a s"

text \<open>
  \textbf{Step A} Implement the function @{text normal} which returns @{const True} only when the
  arithmetic expression is normalized.
\<close>

fun normal :: "aexp \<Rightarrow> bool" where
  "normal a = undefined"

text \<open>
  \textbf{Step B} Implement the function @{text normallize} which translates an arbitrary arithmetic
  expression intro a normalized arithmetic expression.
\<close>

fun normalize :: "aexp \<Rightarrow> aexp" where
  "normalize a = undefined"

text \<open>
  \textbf{Step C} Prove that @{const normalize} does not change the result of the arithmetic
  expression.
\<close>

lemma "aval (normalize a) s = aval a s"
  oops

text \<open>
  \textbf{Step D} Prove that @{const normalize} does indeed return a normalized arithmetic
  expression.
\<close>

lemma "normal (normalize a)"
  oops

end

