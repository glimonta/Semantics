(*<*)
theory sol03
imports "~~/src/HOL/IMP/BExp" "~~/src/HOL/IMP/ASM"
begin
(*>*)
text {* \ExerciseSheet{3}{29.~10.~2013} *}




text {* \Exercise{Relational @{text "aval"}}

  Theory @{text AExp} defines an evaluation function
  @{text "aval :: aexp \<Rightarrow> state \<Rightarrow> val"} for arithmetic expressions.
  Define a corresponding evaluation relation
  @{text "is_aval :: aexp \<Rightarrow> state \<Rightarrow> val \<Rightarrow> bool"} as an inductive predicate:
*}

inductive is_aval :: "aexp \<Rightarrow> state \<Rightarrow> val \<Rightarrow> bool" (*<*)where
  "is_aval (N n) s n" |
  "s x = v \<Longrightarrow> is_aval (V x) s v" |
  "\<lbrakk>is_aval a1 s v1; is_aval a2 s v2; v'=v1+v2\<rbrakk> \<Longrightarrow> is_aval (Plus a1 a2) s v'"
(*>*)

text {* Use the introduction rules @{text is_aval.intros} to prove
  this example lemma. *}

lemma "is_aval (Plus (N 2) (Plus (V x) (N 3))) s (2 + (s x + 3))"
(*<*) by (auto intro!: is_aval.intros) (*>*)

text {* Prove that the evaluation relation @{text is_aval} agrees with
  the evaluation function @{text aval}. Show implications in both
  directions, and then prove the if-and-only-if form.
*}

lemma aval1: "is_aval a s v \<Longrightarrow> aval a s = v"
(*<*) by (induction rule: is_aval.induct) auto (*>*)

lemma aval2: "aval a s = v \<Longrightarrow> is_aval a s v"
(*<*) by (induction a arbitrary: v) (auto intro: is_aval.intros) (*>*)

theorem "is_aval a s v \<longleftrightarrow> aval a s = v"
(*<*)
proof
  assume "is_aval a s v" thus "aval a s = v" by (rule aval1)
next
  assume "aval a s = v" thus "is_aval a s v" by (rule aval2)
qed
(*>*)

(*<*)
(*The version without equality assumptions also works.*)
inductive is_aval' :: "aexp \<Rightarrow> state \<Rightarrow> val \<Rightarrow> bool" where
  "is_aval' (N n) s n" |
  "is_aval' (V x) s (s x)" |
  "\<lbrakk>is_aval' a1 s v1; is_aval' a2 s v2\<rbrakk> \<Longrightarrow> is_aval' (Plus a1 a2) s (v1 + v2)"

lemma "is_aval' (Plus (V x) (Plus (V y) (N 3))) s (s x + (s y + 3))"
by (auto intro!: is_aval'.intros)

theorem "is_aval' a s v \<longleftrightarrow> aval a s = v"
  apply (rule iffI)
  apply (induction rule: is_aval'.induct)
  apply auto
  apply (induction a arbitrary: v)
  apply (auto intro: is_aval'.intros)
  done
(*>*)


text {* \Exercise{Avoiding Stack Underflow}*}

text {* A \emph{stack underflow} occurs when executing an instruction
  on a stack containing too few values -- e.g., executing an @{text ADD}
  instruction on an stack of size less than two. A well-formed sequence of
  instructions (e.g., one generated by @{text comp}) should never
  cause a stack underflow. *}

(* Alternative: functional solution: *)

text {*
  In this exercise, you will define a semantics for the 
  stack-machine that throws an exception if the program underflows the stack.
*}

text {* Modify the @{text "exec1"} and @{text "exec"} - functions, such
  that they return an option value, @{text "None"} indicating a 
  stack-underflow. *}
fun exec1 :: "instr \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack option" 
(*<*)
where
"exec1 (LOADI n) _ stk  =  Some (n # stk)" |
"exec1 (LOAD x) s stk  =  Some (s(x) # stk)" |
"exec1  ADD _ stk  =  (
  if length (stk)\<ge>2 then 
    Some ((hd2 stk + hd stk) # tl2 stk)
  else None)"
(*>*)

fun exec :: "instr list \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack option"
(*<*)
 where
"exec [] _ stk = Some stk" |
"exec (i#is) s stk = (case exec1 i s stk of
    Some stk \<Rightarrow> exec is s stk
  | None \<Rightarrow> None)"
(*>*)

text {*
  Now adjust the proof of theorem @{text "exec_comp"} to show that programs
  output by the compiler never underflow the stack:
*}
(*<*)
lemma exec_append[simp]:
  "exec (is1@is2) s stk = (case exec is1 s stk of
    Some stk \<Rightarrow> exec is2 s stk
  | None \<Rightarrow> None)"
apply(induction is1 arbitrary: stk)
apply (auto split: option.split)
done
(*>*)
theorem exec_comp: "exec (comp a) s stk = Some (aval a s # stk)"
(*<*)
apply(induction a arbitrary: stk)
apply (auto)
done
(*>*)



(*<*)
(* Alternative: Relational solution *)
text {*
  In this exercise, you will define a relational semantics for the 
  stack-machine. The relation does not contain elements for programs causing
  a stack underflow.
*}

inductive execi1 :: "instr \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack \<Rightarrow> bool" where
  "execi1 (LOADI n) s stk (n#stk)"
| "execi1 (LOAD x) s stk (s x#stk)"
| "execi1 (ADD) _ (v1#v2#stk) ((v1+v2)#stk)"

lemma 
  assumes "execi1 i s stk stk'"  
  shows "ASM.exec1 i s stk = stk'"
  using assms
  by induction auto

lemma 
  assumes "ASM.exec1 i s stk = stk'"
  shows "execi1 i s stk stk'"
  nitpick
  oops

inductive execi :: "instr list \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack \<Rightarrow> bool" where
  "execi [] s stk stk"
| "\<lbrakk> execi1 i s stk stk2; execi is s stk2 stk' \<rbrakk> \<Longrightarrow> execi (i#is) s stk stk'"

lemma execi_appendI: 
  assumes E1: "execi is1 s stk stk2" and E2: "execi is2 s stk2 stk'"
  shows "execi (is1@is2) s stk stk'"
  using E1 E2
  by (induction) (auto intro: execi.intros)

lemma execi_appendE[elim]:
  assumes "execi (is1@is2) s stk stk'"
  obtains stk2 where "execi is1 s stk stk2" and "execi is2 s stk2 stk'"
  using assms
  apply (induction is1 arbitrary: stk)
  apply (auto intro: execi.intros) []
  apply (erule execi.cases)
  apply (auto intro: execi.intros)
  (*apply (force intro: execi.intros elim!: execi.cases)*)
  done

lemma execi_sound:
  shows "execi (comp a) s stk (aval a s # stk)"
  apply (induction a arbitrary: stk)
  apply (auto 
    intro!: execi.intros execi1.intros execi_appendI
    simp: add.commute)
  done

inductive_cases [elim!]: 
  "execi [LOADI i] s stk stk'"
  "execi [LOAD x] s stk stk'"
  "execi [ADD] s stk stk'"
  "execi [] s stk stk'"

lemma execi_complete:
  assumes "execi (comp a) s stk stk'"
  shows "stk' = aval a s#stk"
  using assms
  apply (induction a arbitrary: s stk stk')
  apply (auto elim: execi1.cases)  [2]
  apply (fastforce elim: execi1.cases)
  done

theorem execi_correct:
  "execi (comp a) s stk stk' \<longleftrightarrow> (stk' = aval a s # stk)"
  using execi_sound execi_complete
  by blast
(*>*)


text {* \Exercise{Boolean If expressions}

We consider an alternative definition of boolean expressions, which
  feature a conditional construct: *}

datatype ifexp = Bc' bool | If ifexp ifexp ifexp | Less' aexp aexp

text {*
\begin{enumerate}
\item Define a function @{text ifval} analogous to @{const bval},
  which evaluates @{typ ifexp} expressions.

\item
Define a function @{term translate},
which translates @{typ ifexp}s to @{typ bexp}s.
  State and prove a lemma showing that the translation is correct.
\end{enumerate}
*}
(*<*)
primrec ifval :: "ifexp \<Rightarrow> state \<Rightarrow> bool" where
"ifval (Bc' b) _ = b" |
"ifval (If b1 b2 b3) st = (if ifval b1 st then ifval b2 st else ifval b3 st)" |
"ifval (Less' a1 a2) st = (aval a1 st < aval a2 st)"

fun Or :: "bexp \<Rightarrow> bexp \<Rightarrow> bexp" where
"Or b1 b2 = Not (And (Not b1) (Not b2))"

fun If_bexp :: "bexp \<Rightarrow> bexp \<Rightarrow> bexp \<Rightarrow> bexp" where
"If_bexp b1 b2 b3 = Or (And b1 b2) (And (Not b1) b3)"

primrec translate :: "ifexp \<Rightarrow> bexp" where
"translate (Bc' b) = (Bc b)" |
"translate (If b1 b2 b3) =
  If_bexp (translate b1) (translate b2) (translate b3)" |
"translate (Less' a1 a2) = Less a1 a2"

lemma translate_sound: "bval (translate exp) s = ifval exp s"
by (induction exp) auto
(*>*)

(*<*)
end
(*>*)