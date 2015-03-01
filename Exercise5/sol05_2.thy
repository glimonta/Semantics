theory sol05_2
imports "~~/src/HOL/IMP/BExp" "~~/src/HOL/IMP/Star"
begin

(****************************************)
(** Com.thy **)
(****************************************)

datatype
  com = SKIP 
      | Assign vname aexp       ("_ ::= _" [1000, 61] 61)
      | Seq    com  com         ("_;;/ _"  [60, 61] 60)
      | If     bexp com com     ("(IF _/ THEN _/ ELSE _)"  [0, 0, 61] 61)
      | While  bexp com         ("(WHILE _/ DO _)"  [0, 61] 61)
      | Or     com  com         (infixr "\<parallel>" 62)
      | ASSUME bexp             


(****************************************)
(** Big_Step.thy **)
(****************************************)

subsection "Big-Step Semantics of Commands"

text {*
The big-step semantics is a straight-forward inductive definition
with concrete syntax. Note that the first paramenter is a tuple,
so the syntax becomes @{text "(c,s) \<Rightarrow> s'"}.
*}

text_raw{*\snip{BigStepdef}{0}{1}{% *}
inductive
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
\<Longrightarrow> (WHILE b DO c, s\<^sub>1) \<Rightarrow> s\<^sub>3"
| Or1: "\<lbrakk> (c1,s) \<Rightarrow> s' \<rbrakk> \<Longrightarrow> (c1\<parallel>c2,s) \<Rightarrow> s'"
| Or2: "\<lbrakk> (c2,s) \<Rightarrow> s' \<rbrakk> \<Longrightarrow> (c1\<parallel>c2,s) \<Rightarrow> s'"
| Assume: "\<lbrakk> bval b s \<rbrakk> \<Longrightarrow> (ASSUME b,s) \<Rightarrow> s"
text_raw{*}%endsnip*}

text_raw{*\snip{BigStepEx}{1}{2}{% *}
schematic_lemma ex: "(''x'' ::= N 5;; ''y'' ::= V ''x'', s) \<Rightarrow> ?t"
apply(rule Seq)
apply(rule Assign)
apply simp
apply(rule Assign)
done
text_raw{*}%endsnip*}

thm ex[simplified]

text{* We want to execute the big-step rules: *}

code_pred big_step .

text{* For inductive definitions we need command
       \texttt{values} instead of \texttt{value}. *}

values "{t. (SKIP, \<lambda>_. 0) \<Rightarrow> t}"

text{* We need to translate the result state into a list
to display it. *}

values "{map t [''x''] |t. (SKIP, <''x'' := 42>) \<Rightarrow> t}"

values "{map t [''x''] |t. (''x'' ::= N 2, <''x'' := 42>) \<Rightarrow> t}"

values "{map t [''x'',''y''] |t.
  (WHILE Less (V ''x'') (V ''y'') DO (''x'' ::= Plus (V ''x'') (N 5)),
   <''x'' := 0, ''y'' := 13>) \<Rightarrow> t}"


text{* Proof automation: *}

text {* The introduction rules are good for automatically
construction small program executions. The recursive cases
may require backtracking, so we declare the set as unsafe
intro rules. *}
declare big_step.intros [intro]

text{* The standard induction rule 
@{thm [display] big_step.induct [no_vars]} *}

thm big_step.induct

text{*
This induction schema is almost perfect for our purposes, but
our trick for reusing the tuple syntax means that the induction
schema has two parameters instead of the @{text c}, @{text s},
and @{text s'} that we are likely to encounter. Splitting
the tuple parameter fixes this:
*}
lemmas big_step_induct = big_step.induct[split_format(complete)]
thm big_step_induct
text {*
@{thm [display] big_step_induct [no_vars]}
*}


subsection "Rule inversion"

text{* What can we deduce from @{prop "(SKIP,s) \<Rightarrow> t"} ?
That @{prop "s = t"}. This is how we can automatically prove it: *}

inductive_cases SkipE[elim!]: "(SKIP,s) \<Rightarrow> t"
thm SkipE

text{* This is an \emph{elimination rule}. The [elim] attribute tells auto,
blast and friends (but not simp!) to use it automatically; [elim!] means that
it is applied eagerly.

Similarly for the other commands: *}

inductive_cases AssignE[elim!]: "(x ::= a,s) \<Rightarrow> t"
thm AssignE
inductive_cases SeqE[elim!]: "(c1;;c2,s1) \<Rightarrow> s3"
thm SeqE
inductive_cases IfE[elim!]: "(IF b THEN c1 ELSE c2,s) \<Rightarrow> t"
thm IfE

inductive_cases WhileE[elim]: "(WHILE b DO c,s) \<Rightarrow> t"
thm WhileE
text{* Only [elim]: [elim!] would not terminate. *}

inductive_cases OrE[elim!]: "(c1\<parallel>c2,s) \<Rightarrow> t"
thm OrE

inductive_cases AssumeE[elim!]: "(ASSUME b,s) \<Rightarrow> t"
thm AssumeE

text{* An automatic example: *}

lemma "(IF b THEN SKIP ELSE SKIP, s) \<Rightarrow> t \<Longrightarrow> t = s"
by blast

text{* Rule inversion by hand via the ``cases'' method: *}

lemma assumes "(IF b THEN SKIP ELSE SKIP, s) \<Rightarrow> t"
shows "t = s"
proof-
  from assms show ?thesis
  proof cases  --"inverting assms"
    case IfTrue thm IfTrue
    thus ?thesis by blast
  next
    case IfFalse thus ?thesis by blast
  qed
qed

(* Using rule inversion to prove simplification rules: *)
lemma assign_simp:
  "(x ::= a,s) \<Rightarrow> s' \<longleftrightarrow> (s' = s(x := aval a s))"
  by auto

text {* An example combining rule inversion and derivations *}
lemma Seq_assoc:
  "(c1;; c2;; c3, s) \<Rightarrow> s' \<longleftrightarrow> (c1;; (c2;; c3), s) \<Rightarrow> s'"
proof
  assume "(c1;; c2;; c3, s) \<Rightarrow> s'"
  then obtain s1 s2 where
    c1: "(c1, s) \<Rightarrow> s1" and
    c2: "(c2, s1) \<Rightarrow> s2" and
    c3: "(c3, s2) \<Rightarrow> s'" by auto
  from c2 c3
  have "(c2;; c3, s1) \<Rightarrow> s'" by (rule Seq)
  with c1
  show "(c1;; (c2;; c3), s) \<Rightarrow> s'" by (rule Seq)
next
  -- "The other direction is analogous"
  assume "(c1;; (c2;; c3), s) \<Rightarrow> s'"
  thus "(c1;; c2;; c3, s) \<Rightarrow> s'" by auto
qed


subsection "Command Equivalence"

text {*
  We call two statements @{text c} and @{text c'} equivalent wrt.\ the
  big-step semantics when \emph{@{text c} started in @{text s} terminates
  in @{text s'} iff @{text c'} started in the same @{text s} also terminates
  in the same @{text s'}}. Formally:
*}
text_raw{*\snip{BigStepEquiv}{0}{1}{% *}
abbreviation
  equiv_c :: "com \<Rightarrow> com \<Rightarrow> bool" (infix "\<sim>" 50) where
  "c \<sim> c' \<equiv> (\<forall>s t. (c,s) \<Rightarrow> t  =  (c',s) \<Rightarrow> t)"
text_raw{*}%endsnip*}

text {*
Warning: @{text"\<sim>"} is the symbol written \verb!\ < s i m >! (without spaces).

  As an example, we show that loop unfolding is an equivalence
  transformation on programs:
*}
lemma unfold_while:
  "(WHILE b DO c) \<sim> (IF b THEN c;; WHILE b DO c ELSE SKIP)" (is "?w \<sim> ?iw")
proof -
  -- "to show the equivalence, we look at the derivation tree for"
  -- "each side and from that construct a derivation tree for the other side"
  { fix s t assume "(?w, s) \<Rightarrow> t"
    -- "as a first thing we note that, if @{text b} is @{text False} in state @{text s},"
    -- "then both statements do nothing:"
    { assume "\<not>bval b s"
      hence "t = s" using `(?w,s) \<Rightarrow> t` by blast
      hence "(?iw, s) \<Rightarrow> t" using `\<not>bval b s` by blast
    }
    moreover
    -- "on the other hand, if @{text b} is @{text True} in state @{text s},"
    -- {* then only the @{text WhileTrue} rule can have been used to derive @{text "(?w, s) \<Rightarrow> t"} *}
    { assume "bval b s"
      with `(?w, s) \<Rightarrow> t` obtain s' where
        "(c, s) \<Rightarrow> s'" and "(?w, s') \<Rightarrow> t" by auto
      -- "now we can build a derivation tree for the @{text IF}"
      -- "first, the body of the True-branch:"
      hence "(c;; ?w, s) \<Rightarrow> t" by (rule Seq)
      -- "then the whole @{text IF}"
      with `bval b s` have "(?iw, s) \<Rightarrow> t" by (rule IfTrue)
    }
    ultimately
    -- "both cases together give us what we want:"
    have "(?iw, s) \<Rightarrow> t" by blast
  }
  moreover
  -- "now the other direction:"
  { fix s t assume "(?iw, s) \<Rightarrow> t"
    -- "again, if @{text b} is @{text False} in state @{text s}, then the False-branch"
    -- "of the @{text IF} is executed, and both statements do nothing:"
    { assume "\<not>bval b s"
      hence "s = t" using `(?iw, s) \<Rightarrow> t` by blast
      hence "(?w, s) \<Rightarrow> t" using `\<not>bval b s` by blast
    }
    moreover
    -- "on the other hand, if @{text b} is @{text True} in state @{text s},"
    -- {* then this time only the @{text IfTrue} rule can have be used *}
    { assume "bval b s"
      with `(?iw, s) \<Rightarrow> t` have "(c;; ?w, s) \<Rightarrow> t" by auto
      -- "and for this, only the Seq-rule is applicable:"
      then obtain s' where
        "(c, s) \<Rightarrow> s'" and "(?w, s') \<Rightarrow> t" by auto
      -- "with this information, we can build a derivation tree for the @{text WHILE}"
      with `bval b s`
      have "(?w, s) \<Rightarrow> t" by (rule WhileTrue)
    }
    ultimately
    -- "both cases together again give us what we want:"
    have "(?w, s) \<Rightarrow> t" by blast
  }
  ultimately
  show ?thesis by blast
qed

text {* Luckily, such lengthy proofs are seldom necessary.  Isabelle can
prove many such facts automatically.  *}

lemma while_unfold:
  "(WHILE b DO c) \<sim> (IF b THEN c;; WHILE b DO c ELSE SKIP)"
by blast

lemma triv_if:
  "(IF b THEN c ELSE c) \<sim> c"
by blast

lemma commute_if:
  "(IF b1 THEN (IF b2 THEN c11 ELSE c12) ELSE c2) 
   \<sim> 
   (IF b2 THEN (IF b1 THEN c11 ELSE c2) ELSE (IF b1 THEN c12 ELSE c2))"
by blast

lemma sim_while_cong_aux:
  "(WHILE b DO c,s) \<Rightarrow> t  \<Longrightarrow> c \<sim> c' \<Longrightarrow>  (WHILE b DO c',s) \<Rightarrow> t"
apply(induction "WHILE b DO c" s t arbitrary: b c rule: big_step_induct)
 apply blast
apply blast
done

lemma sim_while_cong: "c \<sim> c' \<Longrightarrow> WHILE b DO c \<sim> WHILE b DO c'"
by (metis sim_while_cong_aux)

text {* Command equivalence is an equivalence relation, i.e.\ it is
reflexive, symmetric, and transitive. Because we used an abbreviation
above, Isabelle derives this automatically. *}

lemma sim_refl:  "c \<sim> c" by simp
lemma sim_sym:   "(c \<sim> c') = (c' \<sim> c)" by auto
lemma sim_trans: "c \<sim> c' \<Longrightarrow> c' \<sim> c'' \<Longrightarrow> c \<sim> c''" by auto


lemma "c1 \<parallel> c2 \<sim> c2 \<parallel> c1"
  by blast

lemma "(IF b THEN c1 ELSE c2) \<sim> ((ASSUME b;; c1) \<parallel> (ASSUME (Not b);; c2))"
  by fastforce



subsection "Execution is deterministic"
(** Not any more! **)

(****************************************)
(** Small_Step.thy **)
(****************************************)

subsection "The transition relation"

text_raw{*\snip{SmallStepDef}{0}{2}{% *}
inductive
  small_step :: "com * state \<Rightarrow> com * state \<Rightarrow> bool" (infix "\<rightarrow>" 55)
where
Assign:  "(x ::= a, s) \<rightarrow> (SKIP, s(x := aval a s))" |

Seq1:    "(SKIP;;c\<^sub>2,s) \<rightarrow> (c\<^sub>2,s)" |
Seq2:    "(c\<^sub>1,s) \<rightarrow> (c\<^sub>1',s') \<Longrightarrow> (c\<^sub>1;;c\<^sub>2,s) \<rightarrow> (c\<^sub>1';;c\<^sub>2,s')" |

IfTrue:  "bval b s \<Longrightarrow> (IF b THEN c\<^sub>1 ELSE c\<^sub>2,s) \<rightarrow> (c\<^sub>1,s)" |
IfFalse: "\<not>bval b s \<Longrightarrow> (IF b THEN c\<^sub>1 ELSE c\<^sub>2,s) \<rightarrow> (c\<^sub>2,s)" |

While:   "(WHILE b DO c,s) \<rightarrow>
            (IF b THEN c;; WHILE b DO c ELSE SKIP,s)"
| Or1: "(c1\<parallel>c2,s) \<rightarrow> (c1,s)"
| Or2: "(c1\<parallel>c2,s) \<rightarrow> (c2,s)"
| Assume: "bval b s \<Longrightarrow> (ASSUME b,s) \<rightarrow> (SKIP,s)"
text_raw{*}%endsnip*}


abbreviation
  small_steps :: "com * state \<Rightarrow> com * state \<Rightarrow> bool" (infix "\<rightarrow>*" 55)
where "x \<rightarrow>* y == star small_step x y"

subsection{* Executability *}

code_pred small_step .

values "{(c',map t [''x'',''y'',''z'']) |c' t.
   (''x'' ::= V ''z'';; ''y'' ::= V ''x'',
    <''x'' := 3, ''y'' := 7, ''z'' := 5>) \<rightarrow>* (c',t)}"


subsection{* Proof infrastructure *}

subsubsection{* Induction rules *}

text{* The default induction rule @{thm[source] small_step.induct} only works
for lemmas of the form @{text"a \<rightarrow> b \<Longrightarrow> \<dots>"} where @{text a} and @{text b} are
not already pairs @{text"(DUMMY,DUMMY)"}. We can generate a suitable variant
of @{thm[source] small_step.induct} for pairs by ``splitting'' the arguments
@{text"\<rightarrow>"} into pairs: *}
lemmas small_step_induct = small_step.induct[split_format(complete)]


subsubsection{* Proof automation *}

declare small_step.intros[simp,intro]

text{* Rule inversion: *}

inductive_cases ssSkipE[elim!]: "(SKIP,s) \<rightarrow> ct"
thm ssSkipE
inductive_cases ssAssignE[elim!]: "(x::=a,s) \<rightarrow> ct"
thm ssAssignE
inductive_cases ssSeqE[elim]: "(c1;;c2,s) \<rightarrow> ct"
thm ssSeqE
inductive_cases ssIfE[elim!]: "(IF b THEN c1 ELSE c2,s) \<rightarrow> ct"

inductive_cases ssWhileE[elim]: "(WHILE b DO c, s) \<rightarrow> ct"

inductive_cases ssOrE[elim!]: "(c1\<parallel>c2,s) \<rightarrow> ct"
inductive_cases ssAssumeE[elim!]: "(ASSUME b,s) \<rightarrow> ct"

(** Does not hold any more.
text{* A simple property: *}
lemma deterministic:
  "cs \<rightarrow> cs' \<Longrightarrow> cs \<rightarrow> cs'' \<Longrightarrow> cs'' = cs'"
apply(induction arbitrary: cs'' rule: small_step.induct)
apply blast+
done
**)

subsection "Equivalence with big-step semantics"

lemma star_seq2: "(c1,s) \<rightarrow>* (c1',s') \<Longrightarrow> (c1;;c2,s) \<rightarrow>* (c1';;c2,s')"
proof(induction rule: star_induct)
  case refl thus ?case by simp
next
  case step
  thus ?case by (metis Seq2 star.step)
qed

lemma seq_comp:
  "\<lbrakk> (c1,s1) \<rightarrow>* (SKIP,s2); (c2,s2) \<rightarrow>* (SKIP,s3) \<rbrakk>
   \<Longrightarrow> (c1;;c2, s1) \<rightarrow>* (SKIP,s3)"
by(blast intro: star.step star_seq2 star_trans)

text{* The following proof corresponds to one on the board where one would
show chains of @{text "\<rightarrow>"} and @{text "\<rightarrow>*"} steps. *}

lemma big_to_small:
  "cs \<Rightarrow> t \<Longrightarrow> cs \<rightarrow>* (SKIP,t)"
proof (induction rule: big_step.induct)
  fix s show "(SKIP,s) \<rightarrow>* (SKIP,s)" by simp
next
  fix x a s show "(x ::= a,s) \<rightarrow>* (SKIP, s(x := aval a s))" by auto
next
  fix c1 c2 s1 s2 s3
  assume "(c1,s1) \<rightarrow>* (SKIP,s2)" and "(c2,s2) \<rightarrow>* (SKIP,s3)"
  thus "(c1;;c2, s1) \<rightarrow>* (SKIP,s3)" by (rule seq_comp)
next
  fix s::state and b c0 c1 t
  assume "bval b s"
  hence "(IF b THEN c0 ELSE c1,s) \<rightarrow> (c0,s)" by simp
  moreover assume "(c0,s) \<rightarrow>* (SKIP,t)"
  ultimately 
  show "(IF b THEN c0 ELSE c1,s) \<rightarrow>* (SKIP,t)" by (metis star.simps)
next
  fix s::state and b c0 c1 t
  assume "\<not>bval b s"
  hence "(IF b THEN c0 ELSE c1,s) \<rightarrow> (c1,s)" by simp
  moreover assume "(c1,s) \<rightarrow>* (SKIP,t)"
  ultimately 
  show "(IF b THEN c0 ELSE c1,s) \<rightarrow>* (SKIP,t)" by (metis star.simps)
next
  fix b c and s::state
  assume b: "\<not>bval b s"
  let ?if = "IF b THEN c;; WHILE b DO c ELSE SKIP"
  have "(WHILE b DO c,s) \<rightarrow> (?if, s)" by blast
  moreover have "(?if,s) \<rightarrow> (SKIP, s)" by (simp add: b)
  ultimately show "(WHILE b DO c,s) \<rightarrow>* (SKIP,s)" by(metis star.refl star.step)
next
  fix b c s s' t
  let ?w  = "WHILE b DO c"
  let ?if = "IF b THEN c;; ?w ELSE SKIP"
  assume w: "(?w,s') \<rightarrow>* (SKIP,t)"
  assume c: "(c,s) \<rightarrow>* (SKIP,s')"
  assume b: "bval b s"
  have "(?w,s) \<rightarrow> (?if, s)" by blast
  moreover have "(?if, s) \<rightarrow> (c;; ?w, s)" by (simp add: b)
  moreover have "(c;; ?w,s) \<rightarrow>* (SKIP,t)" by(rule seq_comp[OF c w])
  ultimately show "(WHILE b DO c,s) \<rightarrow>* (SKIP,t)" by (metis star.simps)
next
  fix c1 s s' c2
  have "(c1 \<parallel> c2,s) \<rightarrow> (c1,s)" by rule
  moreover assume "(c1, s) \<rightarrow>* (SKIP, s')"
  ultimately show "(c1 \<parallel> c2, s) \<rightarrow>* (SKIP, s')"
    by rule
next
  fix c1 s s' c2
  have "(c1 \<parallel> c2,s) \<rightarrow> (c2,s)" by rule
  moreover assume "(c2, s) \<rightarrow>* (SKIP, s')"
  ultimately show "(c1 \<parallel> c2, s) \<rightarrow>* (SKIP, s')"
    by rule
next
  fix b s
  assume "bval b s"
  hence "(ASSUME b, s) \<rightarrow> (SKIP, s)" by rule
  thus "(ASSUME b, s) \<rightarrow>* (SKIP, s)" by rule
qed

text{* Each case of the induction can be proved automatically: *}
lemma  "cs \<Rightarrow> t \<Longrightarrow> cs \<rightarrow>* (SKIP,t)"
proof (induction rule: big_step.induct)
  case Skip show ?case by blast
next
  case Assign show ?case by blast
next
  case Seq thus ?case by (blast intro: seq_comp)
next
  case IfTrue thus ?case by (blast intro: star.step)
next
  case IfFalse thus ?case by (blast intro: star.step)
next
  case WhileFalse thus ?case
    by (metis star.step star_step1 small_step.IfFalse small_step.While)
next
  case WhileTrue
  thus ?case
    by(metis While seq_comp small_step.IfTrue star.step[of small_step])
next
  case Or1 thus ?case
    by (metis small_step.Or1 star.simps)
next
  case Or2 thus ?case
    by (metis small_step.Or2 star.simps)
next
  case Assume thus ?case by blast
qed 

lemma small1_big_continue:
  "cs \<rightarrow> cs' \<Longrightarrow> cs' \<Rightarrow> t \<Longrightarrow> cs \<Rightarrow> t"
apply (induction arbitrary: t rule: small_step.induct)
apply auto
done

lemma small_big_continue:
  "cs \<rightarrow>* cs' \<Longrightarrow> cs' \<Rightarrow> t \<Longrightarrow> cs \<Rightarrow> t"
apply (induction rule: star.induct)
apply (auto intro: small1_big_continue)
done

lemma small_to_big: "cs \<rightarrow>* (SKIP,t) \<Longrightarrow> cs \<Rightarrow> t"
by (metis small_big_continue Skip)

text {*
  Finally, the equivalence theorem:
*}
theorem big_iff_small:
  "cs \<Rightarrow> t = cs \<rightarrow>* (SKIP,t)"
by(metis big_to_small small_to_big)


subsection "Final configurations and infinite reductions"

(** Does not hold any more
definition "final cs \<longleftrightarrow> \<not>(EX cs'. cs \<rightarrow> cs')"

lemma finalD: "final (c,s) \<Longrightarrow> c = SKIP"
apply(simp add: final_def)
apply(induction c)
apply blast+
done

lemma final_iff_SKIP: "final (c,s) = (c = SKIP)"
by (metis ssSkipE finalD final_def)

text{* Now we can show that @{text"\<Rightarrow>"} yields a final state iff @{text"\<rightarrow>"}
terminates: *}

lemma big_iff_small_termination:
  "(EX t. cs \<Rightarrow> t) \<longleftrightarrow> (EX cs'. cs \<rightarrow>* cs' \<and> final cs')"
by(simp add: big_iff_small final_iff_SKIP)

text{* This is the same as saying that the absence of a big step result is
equivalent with absence of a terminating small step sequence, i.e.\ with
nontermination.  Since @{text"\<rightarrow>"} is determininistic, there is no difference
between may and must terminate. *}
**)

end
