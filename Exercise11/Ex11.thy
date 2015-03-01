(*<*)
theory Ex11
imports "~~/src/HOL/IMP/Hoare_Sound_Complete" "~~/src/HOL/IMP/VCG"
begin
(*>*)
text {* \ExerciseSheet{11}{13.~1.~2015} *}

text {*
  \Exercise{Forward Assignment Rule}

  Think up and prove a forward assignment rule, i.e., a rule of the
  form @{text "\<turnstile> {P} x::=a {\<dots>}"}, where @{text "\<dots>"} is some suitable
  postcondition. Hint: To prove this rule, use the completeness
  property, and prove the rule semantically.
*}
lemma fwd_Assign: "\<turnstile> {P} x::=a { \<lambda>s' . EX s. P s \<and> s' = s[a/x] }" (* s' = s(x:= aval a s) *)
  apply (rule hoare_complete)
  unfolding hoare_valid_def
  by auto

lemmas fwd_Assign' = weaken_post[OF fwd_Assign]

text {* Redo the proofs for @{text "MAX"} and @{text "MUL"} from the previous
  exercise sheet, this time using your forward assignment rule. 
*}
definition MAX :: com where
  "MAX \<equiv> 
  IF (Less (V ''a'') (V ''b'')) THEN 
    ''c''::=V ''b'' 
  ELSE
    ''c''::=V ''a''"

lemma "\<turnstile> {\<lambda>s. True} MAX {\<lambda>s. s ''c'' = max (s ''a'') (s ''b'')}"
  unfolding MAX_def
  apply (rule hoare.If)
  apply (rule fwd_Assign')
(*  apply (simp) *)
  apply (auto)
  apply (rule fwd_Assign')
(*  apply (simp) *)
  apply (auto)
done

definition MUL :: com where
  "MUL \<equiv> 
  ''z''::=N 0;;
  ''c''::=N 0;;
  WHILE (Less (V ''c'') (V ''y'')) DO (
    ''z''::=Plus (V ''z'') (V ''x'');;
    ''c''::=Plus (V ''c'') (N 1))"

lemma "\<turnstile> {\<lambda>s. 0 \<le> s ''y''} MUL {\<lambda>s. s ''z'' = s ''x'' * s ''y''}"
  unfolding MUL_def
  apply (rule hoare.Seq)
  apply (rule hoare.Seq)
  apply (rule fwd_Assign)
  apply (auto)
  apply (rule fwd_Assign)
  apply (auto)
  apply (rule strengthen_pre)
  prefer 2
  apply (rule While'[where P="\<lambda>s. s ''z'' = s ''x'' * s ''c''\<and> s ''c'' \<le> s ''y''"])
  apply (rule hoare.Seq)
  apply (rule fwd_Assign)
  apply (rule fwd_Assign')
  apply (auto simp: algebra_simps)
done

text {*
  \Exercise{Using the VCG}

  For each of the three programs given here, you must prove partial
  correctness. You should first write an annotated program, and then use
  the verification condition generator from @{text "VCG.thy"}.
*}

text{* \paragraph{Preliminaries.}  *}

text {* Some abbreviations, freeing us from having to write double quotes
for concrete variable names: *}

abbreviation "aa \<equiv> ''a''"  abbreviation "bb \<equiv> ''b''" abbreviation "cc \<equiv> ''c''"
abbreviation "dd \<equiv> ''d''"  abbreviation "ee \<equiv> ''e''" abbreviation "ff \<equiv> ''f''"
abbreviation "pp \<equiv> ''p''"  abbreviation "qq \<equiv> ''q''" abbreviation "rr \<equiv> ''r''"

text {* Some useful simplification rules: *}
declare algebra_simps[simp]  declare power2_eq_square[simp]

text {* A convenient loop construct: *}

abbreviation For :: "vname \<Rightarrow> aexp \<Rightarrow> aexp \<Rightarrow> com \<Rightarrow> com"
  ("(FOR _/ FROM _/ TO _/ DO _)"  [0, 0, 0, 61] 61) where
  "FOR v FROM a1 TO a2 DO c \<equiv>
     v ::= a1 ;;  WHILE (Less (V v) a2) DO (c ;; v ::= Plus (V v) (N 1))"

abbreviation Afor :: "assn \<Rightarrow> vname \<Rightarrow> aexp \<Rightarrow> aexp \<Rightarrow> acom \<Rightarrow> acom"
  ("({_}/ FOR _/ FROM _/ TO _/ DO _)"  [0, 0, 0, 0, 61] 61) where
  "{b} FOR v FROM a1 TO a2 DO c \<equiv>
     v ::= a1 ;;  {b} WHILE (Less (V v) a2) DO (c ;; v ::= Plus (V v) (N 1))"


text {* \paragraph{Multiplication.} Consider the following program
@{text "MULT"} for performing multiplication and the following assertions
@{text "P_MULT"} and @{text "Q_MULT"}: *}

definition MULT :: com where  "MULT \<equiv> 
  cc ::= N 0 ;; 
  FOR dd FROM (N 0) TO (V aa) DO
    cc ::= Plus (V cc) (V bb)"

definition P_MULT :: "int \<Rightarrow> int \<Rightarrow> assn" where
"P_MULT i j \<equiv> \<lambda>s. s aa = i \<and> s bb = j \<and> 0 \<le> i"

definition Q_MULT :: "int \<Rightarrow> int \<Rightarrow> assn" where
"Q_MULT i j \<equiv> \<lambda>s. s cc = i * j \<and> s aa = i \<and> s bb = j"

text {* Define an annotated program
@{text "AMULT i j"}, so that when the annotations are stripped away, it
yields @{text "MULT"}. (The parameters @{text "i"} and @{text "j"}
will appear only in the loop annotations.) *}

text{* Hint: The program @{text "AMULT i j"} will be essentially @{text "MULT"}
with an invariant annotation @{text "iMULT i j"} at the FOR loop, which you have to
define: *}
definition iMULT :: "int \<Rightarrow> int \<Rightarrow> assn" where
  "iMULT i j \<equiv> \<lambda>s. s aa = i \<and> s bb = j \<and> s cc = s dd * j \<and> s dd \<le> i"

definition AMULT :: "int \<Rightarrow> int \<Rightarrow> acom" where 
  "AMULT i j \<equiv> 
  (cc ::= N 0) ;; 
  {iMULT i j} FOR dd FROM (N 0) TO (V aa) DO
    cc ::= Plus (V cc) (V bb)"

lemmas MULT_defs = MULT_def P_MULT_def Q_MULT_def iMULT_def AMULT_def

lemma strip_AMULT: "strip (AMULT i j) = MULT"
  unfolding MULT_defs
  by simp

text {* Once you have the correct loop annotations, then the partial
correctness proof can be done in two steps, with the help of lemma
@{text "vc_sound'"}. *}

lemma MULT_correct: "\<turnstile> {P_MULT i j} MULT {Q_MULT i j}"
  unfolding strip_AMULT[of i j, symmetric]
  apply(rule vc_sound')
  unfolding MULT_defs
  by auto
(* Si obtenemos algo que creemos que es incorrecto tenemos que revisar las premisas para ver porque
   probablemente hay algo contradictorio ahi. Es buena idea intentar generalizar la postcondicion *)

text {* \paragraph{Division.} Define an annotated version of this
division program, which yields the quotient and remainder of @{text "aa/bb"}
in variables @{text "''q''"} and @{text "''r''"},
respectively. *}

definition DIV :: com where "DIV \<equiv> 
  qq ::= N 0 ;; 
  rr ::= N 0 ;; 
  FOR cc FROM (N 0) TO (V aa) DO (
    rr ::= Plus (V rr) (N 1) ;;
    IF Less (V rr) (V bb) THEN 
      Com.SKIP
    ELSE (
      rr ::= N 0 ;; 
      qq ::= Plus (V qq) (N 1))
  )"

definition P_DIV :: "int \<Rightarrow> int \<Rightarrow> assn" where
"P_DIV i j \<equiv> \<lambda>s. s aa = i \<and> s bb = j \<and> 0 \<le> i \<and> 0 < j"
definition Q_DIV :: "int \<Rightarrow> int \<Rightarrow> assn" where
"Q_DIV i j \<equiv>
  \<lambda> s. i = s qq * j + s rr \<and> 0 \<le> s rr \<and> s rr < j \<and> s aa = i \<and> s bb = j"

definition iDIV :: "int \<Rightarrow> int \<Rightarrow> assn" where
"iDIV i j \<equiv>
  \<lambda> s. s aa = i \<and> s bb = j \<and> s rr \<ge> 0 \<and> s rr < j \<and> s cc = s qq * j + s rr \<and> s cc \<le> i"

text{* *}
definition ADIV :: "int \<Rightarrow> int \<Rightarrow> acom" where "ADIV i j \<equiv> 
  qq ::= N 0 ;;
  rr ::= N 0 ;; 
  {iDIV i j} FOR cc FROM (N 0) TO (V aa) DO (
    rr ::= Plus (V rr) (N 1) ;;
    IF Less (V rr) (V bb) THEN 
      SKIP
    ELSE (
      rr ::= N 0 ;; 
      qq ::= Plus (V qq) (N 1)
    )
  )"

lemma strip_ADIV: "strip (ADIV i j) = DIV"
  unfolding DIV_def
  unfolding ADIV_def
  unfolding P_DIV_def
  unfolding Q_DIV_def
  unfolding iDIV_def
  by auto

lemma DIV_correct: "\<turnstile> {P_DIV i j} DIV {Q_DIV i j}"
  unfolding strip_ADIV[of i j, symmetric]
  apply(rule vc_sound')
  unfolding DIV_def
  unfolding ADIV_def
  unfolding P_DIV_def
  unfolding Q_DIV_def
  unfolding iDIV_def
  by (auto)

text {* \paragraph{Square roots.} Define an annotated version of this
square root program, which yields the square root of input @{text "aa"}
(rounded down to the next integer) in output @{text "bb"}.
*}

definition SQR :: com where "SQR \<equiv> 
  bb ::= N 0 ;;
  cc ::= N 1 ;; 
  WHILE (Not (Less (V aa) (V cc))) DO (
    bb ::= Plus (V bb) (N 1);;
    cc ::= Plus (V cc) (Plus (V bb) (Plus (V bb) (N 1)))
  )"

definition P_SQR :: "int \<Rightarrow> assn" where
"P_SQR i \<equiv> \<lambda>s. s aa = i \<and> 0 \<le> i"
definition Q_SQR :: "int \<Rightarrow> assn" where
"Q_SQR i \<equiv> \<lambda>s. s aa = i \<and> (s bb)^2 \<le> i \<and> i < (s bb + 1)^2"
                                                            
definition iSQR :: "int \<Rightarrow> assn" where
  "iSQR i \<equiv> \<lambda>s. s aa = i \<and> (s bb)^2 \<le> i \<and> (s bb + 1)^2 = s cc"

definition ASQR :: "int \<Rightarrow> acom" where "ASQR i \<equiv> 
  bb ::= N 0 ;; 
  cc ::= N 1 ;; 
  {iSQR i} WHILE (Not (Less (V aa) (V cc))) DO (
    bb ::= Plus (V bb) (N 1);;
    cc ::= Plus (V cc) (Plus (V bb) (Plus (V bb) (N 1)))
  )"

lemma strip_ASQR: "strip (ASQR i) = SQR"
  unfolding SQR_def P_SQR_def Q_SQR_def iSQR_def ASQR_def
  by auto

lemma SQR_correct: "\<turnstile> {P_SQR i} SQR {Q_SQR i}"
  unfolding strip_ASQR[of i, symmetric]
  apply(rule vc_sound')
  unfolding SQR_def P_SQR_def Q_SQR_def iSQR_def ASQR_def
  by (auto)

end
