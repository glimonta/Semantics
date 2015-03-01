header "Compiler for IMP"

theory sol06_1 imports "~~/src/HOL/IMP/Big_Step" "~~/src/HOL/IMP/Star"
begin

text {* \Exercise{A different instruction set architecture}

We consider a different instruction set which evaluates
boolean expressions on the stack, similar to arithmetic expressions:
\begin{itemize}
\item
The boolean value @{term False} is represented by the number @{text 0},
the boolean value @{term True} is represented by any number not equal
to @{text 0}.
\item
For every boolean operation exists a corresponding instruction which,
similar to arithmetic instructions, operates on values on top of the
stack.
\item
The new instruction set introduces a conditional jump which pops the
top-most element from the stack and jumps over a given amount of
instructions, if the popped value corresponds to @{text False}, and
otherwise goes to the next instruction.
\end{itemize}

Modify the theory @{text Compiler} by defining a suitable set of
instructions, by adapting the execution model and the compiler and
by updating the correctness proof.

*}


subsection "List setup"

text {* 
  In the following, we use the length of lists as integers 
  instead of natural numbers. Instead of converting @{typ nat}
  to @{typ int} explicitly, we tell Isabelle to coerce @{typ nat}
  automatically when necessary.
*}
declare [[coercion_enabled]] 
declare [[coercion "int :: nat \<Rightarrow> int"]]

text {* 
  Similarly, we will want to access the ith element of a list, 
  where @{term i} is an @{typ int}.
*}
fun inth :: "'a list \<Rightarrow> int \<Rightarrow> 'a" (infixl "!!" 100) where
"(x # xs) !! i = (if i = 0 then x else xs !! (i - 1))"

text {*
  The only additional lemma we need about this function 
  is indexing over append:
*}
lemma inth_append [simp]:
  "0 \<le> i \<Longrightarrow>
  (xs @ ys) !! i = (if i < size xs then xs !! i else ys !! (i - size xs))"
by (induction xs arbitrary: i) (auto simp: algebra_simps)

text{* We hide coercion @{const int} applied to @{const length}: *}

abbreviation (output)
  "isize xs == int (length xs)"

notation isize ("size")


subsection "Instructions and Stack Machine"

(* MODIFICATION: Changed instruction set *)
text_raw{*\snip{instrdef}{0}{1}{% *}
datatype instr = 
  LOADI int | LOAD vname | ADD | STORE vname |
  AND | NOT | LESS | JFALSE int |
  JMP int 
text_raw{*}%endsnip*}

type_synonym stack = "val list"
type_synonym config = "int \<times> state \<times> stack"

abbreviation "hd2 xs == hd(tl xs)"
abbreviation "tl2 xs == tl(tl xs)"

(* MODIFICATION: Semantics for new instructions *)
fun iexec :: "instr \<Rightarrow> config \<Rightarrow> config" where
"iexec instr (i,s,stk) = (case instr of
  LOADI n \<Rightarrow> (i+1,s, n#stk) |
  LOAD x \<Rightarrow> (i+1,s, s x # stk) |
  ADD \<Rightarrow> (i+1,s, (hd2 stk + hd stk) # tl2 stk) |
  STORE x \<Rightarrow> (i+1,s(x := hd stk),tl stk) |
  AND \<Rightarrow> (i+1,s,(if hd stk \<noteq> 0 \<and> hd2 stk \<noteq> 0 then 1 else 0)#tl2 stk) |
  NOT \<Rightarrow> (i+1,s,(if hd stk \<noteq> 0 then 0 else 1)#tl stk) |
  LESS \<Rightarrow> (i+1,s,(if (hd2 stk < hd stk) then 1 else 0)#tl2 stk) |
  JFALSE n \<Rightarrow> ((if hd stk = 0 then i+1+n else i+1),s,tl stk) |
  JMP n \<Rightarrow>  (i+1+n,s,stk) 
)"

definition
  exec1 :: "instr list \<Rightarrow> config \<Rightarrow> config \<Rightarrow> bool"
     ("(_/ \<turnstile> (_ \<rightarrow>/ _))" [59,0,59] 60) 
where
  "P \<turnstile> c \<rightarrow> c' = 
  (\<exists>i s stk. c = (i,s,stk) \<and> c' = iexec(P!!i) (i,s,stk) \<and> 0 \<le> i \<and> i < size P)"

lemma exec1I [intro, code_pred_intro]:
  "c' = iexec (P!!i) (i,s,stk) \<Longrightarrow> 0 \<le> i \<Longrightarrow> i < size P
  \<Longrightarrow> P \<turnstile> (i,s,stk) \<rightarrow> c'"
by (simp add: exec1_def)

abbreviation 
  exec :: "instr list \<Rightarrow> config \<Rightarrow> config \<Rightarrow> bool" ("(_/ \<turnstile> (_ \<rightarrow>*/ _))" 50)
where
  "exec P \<equiv> star (exec1 P)"

declare star.step[intro]

lemmas exec_induct = star.induct [of "exec1 P", split_format(complete)]

code_pred exec1 by (metis exec1_def)

values
  "{(i,map t [''x'',''y''],stk) | i t stk.
    [LOAD ''y'', STORE ''x''] \<turnstile>
    (0, <''x'' := 3, ''y'' := 4>, []) \<rightarrow>* (i,t,stk)}"


subsection{* Verification infrastructure *}

text{* Below we need to argue about the execution of code that is embedded in
larger programs. For this purpose we show that execution is preserved by
appending code to the left or right of a program. *}

lemma iexec_shift [simp]: 
  "((n+i',s',stk') = iexec x (n+i,s,stk)) = ((i',s',stk') = iexec x (i,s,stk))"
by(auto split:instr.split)

declare [[goals_limit = 1]]
lemma exec1_appendR: "P \<turnstile> c \<rightarrow> c' \<Longrightarrow> P@P' \<turnstile> c \<rightarrow> c'"
  unfolding exec1_def
  by (fastforce split: split_if_asm)

lemma exec_appendR: "P \<turnstile> c \<rightarrow>* c' \<Longrightarrow> P@P' \<turnstile> c \<rightarrow>* c'"
by (induction rule: star.induct) (fastforce intro: exec1_appendR)+

lemma exec1_appendL:
  fixes i i' :: int 
  shows
  "P \<turnstile> (i,s,stk) \<rightarrow> (i',s',stk') \<Longrightarrow>
   P' @ P \<turnstile> (size(P')+i,s,stk) \<rightarrow> (size(P')+i',s',stk')"
  unfolding exec1_def
  by (auto simp del: iexec.simps)

lemma exec_appendL:
  fixes i i' :: int 
  shows
 "P \<turnstile> (i,s,stk) \<rightarrow>* (i',s',stk')  \<Longrightarrow>
  P' @ P \<turnstile> (size(P')+i,s,stk) \<rightarrow>* (size(P')+i',s',stk')"
  by (induction rule: exec_induct) (blast intro!: exec1_appendL)+

text{* Now we specialise the above lemmas to enable automatic proofs of
@{prop "P \<turnstile> c \<rightarrow>* c'"} where @{text P} is a mixture of concrete instructions and
pieces of code that we already know how they execute (by induction), combined
by @{text "@"} and @{text "#"}. Backward jumps are not supported.
The details should be skipped on a first reading.

If we have just executed the first instruction of the program, drop it: *}

lemma exec_Cons_1 [intro]:
  "P \<turnstile> (0,s,stk) \<rightarrow>* (j,t,stk') \<Longrightarrow>
  instr#P \<turnstile> (1,s,stk) \<rightarrow>* (1+j,t,stk')"
by (drule exec_appendL[where P'="[instr]"]) simp

lemma exec_appendL_if[intro]:
  fixes i i' j :: int
  shows
  "size P' <= i
   \<Longrightarrow> P \<turnstile> (i - size P',s,stk) \<rightarrow>* (j,s',stk')
   \<Longrightarrow> i' = size P' + j
   \<Longrightarrow> P' @ P \<turnstile> (i,s,stk) \<rightarrow>* (i',s',stk')"
by (drule exec_appendL[where P'=P']) simp

text{* Split the execution of a compound program up into the excution of its
parts: *}

lemma exec_append_trans[intro]:
  fixes i' i'' j'' :: int
  shows
"P \<turnstile> (0,s,stk) \<rightarrow>* (i',s',stk') \<Longrightarrow>
 size P \<le> i' \<Longrightarrow>
 P' \<turnstile>  (i' - size P,s',stk') \<rightarrow>* (i'',s'',stk'') \<Longrightarrow>
 j'' = size P + i''
 \<Longrightarrow>
 P @ P' \<turnstile> (0,s,stk) \<rightarrow>* (j'',s'',stk'')"
by(metis star_trans[OF exec_appendR exec_appendL_if])

declare Let_def[simp]


subsection "Compilation"

fun acomp :: "aexp \<Rightarrow> instr list" where
"acomp (N n) = [LOADI n]" |
"acomp (V x) = [LOAD x]" |
"acomp (Plus a1 a2) = acomp a1 @ acomp a2 @ [ADD]"

lemma acomp_correct[intro]:
  "acomp a \<turnstile> (0,s,stk) \<rightarrow>* (size(acomp a),s,aval a s#stk)"
by (induction a arbitrary: stk) fastforce+

(* MODIFICATION: Rewritten, similar to acomp *)
fun bcomp :: "bexp \<Rightarrow> instr list" where
  "bcomp (Bc v) = (if v then [LOADI 1] else [LOADI 0])" 
| "bcomp (Not b) = bcomp b@[NOT]"
| "bcomp (And b1 b2) = bcomp b1 @ bcomp b2 @ [AND]"
| "bcomp (Less a1 a2) = acomp a1 @ acomp a2 @ [LESS]"

value
  "bcomp (And (Less (V ''x'') (V ''y'')) (Not(Less (V ''u'') (V ''v''))))"

(* MODIFICATION: Abbreviations to convert between bool and int *)
abbreviation "i2b i \<equiv> i\<noteq>0"
abbreviation "b2i b \<equiv> if b then 1 else 0"

(* MODIFICATION: Lemma similar to acomp_correct *)
lemma bcomp_correct[intro]:
  "bcomp a \<turnstile> (0,s,stk) \<rightarrow>* (size(bcomp a),s,b2i (bval a s)#stk)"
  apply (induction a arbitrary: stk)
  apply (fastforce intro!: exec_append_trans)+
  done

(*
  apply simp_all
  apply force
  apply (fastforce intro!: exec_append_trans)

  apply (fastforce intro!: exec_append_trans)

  apply (fastforce intro!: exec_append_trans)
  done
*)

(* MODIFICATION: Changed IF and WHILE cases *)
fun ccomp :: "com \<Rightarrow> instr list" where
"ccomp SKIP = []" |
"ccomp (x ::= a) = acomp a @ [STORE x]" |
"ccomp (c\<^sub>1;;c\<^sub>2) = ccomp c\<^sub>1 @ ccomp c\<^sub>2" |
"ccomp (IF b THEN c\<^sub>1 ELSE c\<^sub>2) = (
  let cc\<^sub>1 = ccomp c\<^sub>1; 
      cc\<^sub>2 = ccomp c\<^sub>2; 
      cb = bcomp b
   in cb @ JFALSE (size cc\<^sub>1 + 1) # cc\<^sub>1 @ JMP (size cc\<^sub>2) # cc\<^sub>2)" |
"ccomp (WHILE b DO c) =
 (let cc = ccomp c; cb = bcomp b
  in cb @ JFALSE (size cc + 1) # cc @ [JMP (-(size cb + size cc + 2))])"


value "ccomp
 (IF Less (V ''u'') (N 1) THEN ''u'' ::= Plus (V ''u'') (N 1)
  ELSE ''v'' ::= V ''u'')"

value "ccomp (WHILE Less (V ''u'') (N 1) DO (''u'' ::= Plus (V ''u'') (N 1)))"


subsection "Preservation of semantics"

(* MODIFICATION: Changed WHILE_True, added IF-False that is no longer automatic *)
lemma ccomp_bigstep:
  "(c,s) \<Rightarrow> t \<Longrightarrow> ccomp c \<turnstile> (0,s,stk) \<rightarrow>* (size(ccomp c),t,stk)"
proof(induction arbitrary: stk rule: big_step_induct)
  case (Assign x a s)
  show ?case by (fastforce simp:fun_upd_def cong: if_cong)
next
  case (Seq c1 s1 s2 c2 s3)
  let ?cc1 = "ccomp c1"  let ?cc2 = "ccomp c2"
  have "?cc1 @ ?cc2 \<turnstile> (0,s1,stk) \<rightarrow>* (size ?cc1,s2,stk)"
    using Seq.IH(1) by fastforce
  moreover
  have "?cc1 @ ?cc2 \<turnstile> (size ?cc1,s2,stk) \<rightarrow>* (size(?cc1 @ ?cc2),s3,stk)"
    using Seq.IH(2) by fastforce
  ultimately show ?case by simp (blast intro: star_trans)
next
  case (WhileTrue b s1 c s2 s3)
  let ?cc = "ccomp c"
  let ?cb = "bcomp b"
  let ?cw = "ccomp(WHILE b DO c)"
  have "?cw \<turnstile> (0,s1,stk) \<rightarrow>* (size ?cb,s1,1#stk)"
   using `bval b s1` by fastforce
  moreover
  have "?cw \<turnstile> (size ?cb,s1,1#stk) \<rightarrow>* (size ?cb + 1, s1, stk)"
    by fastforce
  moreover have "?cw \<turnstile> (size ?cb + 1, s1, stk) 
    \<rightarrow>* (size ?cb + 1 + size ?cc, s2, stk)"
    using  WhileTrue.IH(1) by fastforce 
  moreover have "?cw \<turnstile> (size ?cb + 1 + size ?cc, s2, stk) \<rightarrow>* (0,s2,stk)"
    by fastforce
  moreover
  have "?cw \<turnstile> (0,s2,stk) \<rightarrow>* (size ?cw,s3,stk)" by(rule WhileTrue.IH(2))
  ultimately show ?case by(blast intro: star_trans)
next
  (* We have to adapt this lemma to work for the Cons (#) operator,
    not only for append (@): *)
  note aux2[intro] = exec_appendL_if[where P'="[instr]" for instr, simplified]

  (* With the adapted lemma in the intro-rules, the proof is automatic again*)
  case (IfFalse b s c2 t c1 stk) 
  thus ?case by fastforce

  (* Alternatively, we can do an isar proof, similar to the WhileTrue case*)

  let ?cc1 = "ccomp c1"
  let ?cc2 = "ccomp c2"
  let ?cb = "bcomp b"
  let ?cw = "ccomp (IF b THEN c1 ELSE c2)"

  have "?cw \<turnstile> (0,s,stk) \<rightarrow>* (size ?cb,s,0#stk)"
    using `\<not>bval b s` by fastforce
  moreover have "?cw \<turnstile> (size ?cb,s,0#stk) \<rightarrow>* (size ?cb + size ?cc1 + 2,s,stk)"
    by fastforce
  moreover have "?cw \<turnstile> (size ?cb + size ?cc1 + 2,s,stk) \<rightarrow>* (size ?cw,t,stk)"
    using IfFalse.IH by fastforce
  ultimately have ?case by(blast intro: star_trans)
qed fastforce+

end

