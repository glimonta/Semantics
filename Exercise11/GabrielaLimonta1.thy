theory GabrielaLimonta1
imports "~~/src/HOL/IMP/Hoare_Sound_Complete" "~~/src/HOL/IMP/VCG"
begin

(* Homework 11.1 *)
abbreviation "xx \<equiv> ''x''" abbreviation "yy \<equiv> ''y''"
abbreviation "aa \<equiv> ''a''" abbreviation "bb \<equiv> ''b''"

definition Cdiff :: com where  "Cdiff \<equiv> 
  bb ::= N 0;;
  WHILE (Less (V bb) (V xx)) DO
    (yy ::= Plus (V yy) (N -1);;
    bb ::= Plus (V bb) (N 1))"

definition P_Cdiff :: "int \<Rightarrow> int \<Rightarrow> assn" where
"P_Cdiff x y \<equiv> \<lambda>s. s xx = x \<and> s yy = y \<and> 0 \<le> x"

definition Q_Cdiff :: "int \<Rightarrow> int \<Rightarrow> assn" where
"Q_Cdiff x y \<equiv> \<lambda>t. t yy = y - x"

definition iCdiff :: "int \<Rightarrow> int \<Rightarrow> assn" where
  "iCdiff x y \<equiv> \<lambda>s. s xx = x \<and> y = s yy + s bb \<and> s bb \<le> x"

definition ACdiff :: "int \<Rightarrow> int \<Rightarrow> acom" where 
  "ACdiff x y \<equiv> 
  (bb ::= N 0) ;;
  {iCdiff x y} WHILE (Less (V bb) (V xx)) DO
    (yy ::= Plus (V yy) (N -1);;
    bb ::= Plus (V bb) (N 1))"

lemma strip_ACdiff: "strip (ACdiff x y) = Cdiff"
  unfolding Cdiff_def P_Cdiff_def Q_Cdiff_def iCdiff_def ACdiff_def
  by simp

lemma Cdiff_correct: "\<turnstile> {P_Cdiff x y} strip (ACdiff x y) {Q_Cdiff x y}"
  unfolding strip_ACdiff[of x y, symmetric]
  apply(rule vc_sound')
  unfolding Cdiff_def P_Cdiff_def Q_Cdiff_def iCdiff_def ACdiff_def
  by auto

end
