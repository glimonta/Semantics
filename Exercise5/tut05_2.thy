header "IMP --- A Simple Imperative Language"

theory tut05_2 imports "~~/src/HOL/IMP/BExp" begin

datatype
  com = SKIP 
      | Assign vname aexp       ("_ ::= _" [1000, 61] 61)
      | Seq    com  com         ("_;;/ _"  [60, 61] 60)
      | If     bexp com com     ("(IF _/ THEN _/ ELSE _)"  [0, 0, 61] 61)
      | While  bexp com         ("(WHILE _/ DO _)"  [0, 61] 61)
      | Or com com              ("_ OR/ _" [55,56] 55)
      | ASSUME bexp

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
| Or1: "\<lbrakk> (c1,s) \<Rightarrow> t \<rbrakk> \<Longrightarrow> (c1 OR c2,s) \<Rightarrow> t"
| Or2: "\<lbrakk> (c2,s) \<Rightarrow> t \<rbrakk> \<Longrightarrow> (c1 OR c2,s) \<Rightarrow> t"
| Assume: "\<lbrakk>bval b s\<rbrakk> \<Longrightarrow> (ASSUME b,s) \<Rightarrow> s"

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

inductive_cases OrE[elim!]: "(Or c1 c2,s) \<Rightarrow> t"
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


lemma "c1 OR c2 \<sim> c2 OR c1"
proof (intro allI iffI)
  fix s t
  assume "(c1 OR c2,s) \<Rightarrow> t"
  thus "(c2 OR c1,s) \<Rightarrow> t"
  proof cases
    case Or1 thus ?thesis by (rule Or2)
  next  
    case Or2 thus ?thesis by (rule Or1)
  qed
qed auto (* Other direction symmetrically*) 

lemma "\<forall>s. s<s+s \<longrightarrow> s>4" (is "\<forall>s. ?P s \<longrightarrow> ?Q s")
proof -
  (* Pattern matching, even higher-order*)
  term ?P
  term ?Q
oops

lemma 
  "IF b THEN c1 ELSE c2 \<sim> ASSUME b;;c1 OR ASSUME (Not b);;c2"
  (is "?l \<sim> ?r")
proof (intro allI iffI)
  fix s t
  assume A: "(?l,s) \<Rightarrow> t"
  thus "(?r,s) \<Rightarrow> t"
  proof cases
    (* Forward-Style*)
    case IfTrue
    hence "(ASSUME b,s) \<Rightarrow> s" by auto
    from this `(c1,s) \<Rightarrow> t` have "(ASSUME b;;c1,s) \<Rightarrow> t" 
      by (rule Seq)
    thus ?thesis by (rule Or1)  
  next
    case IfFalse
    hence A: "(ASSUME (Not b),s) \<Rightarrow> s" by auto
    (* Backward style *)
    show ?thesis
      apply (rule Or2)
      apply (rule Seq)
      apply (rule A)
      apply (rule `(c2,s) \<Rightarrow> t`)
      done
  qed
qed fastforce


end
