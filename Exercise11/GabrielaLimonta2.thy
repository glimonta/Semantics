theory GabrielaLimonta2
imports "~~/src/HOL/IMP/BExp"
begin

(* Homework 11.2 *)

datatype
  com = SKIP 
      | Assign vname aexp       ("_ ::= _" [1000, 61] 61)
      | Seq    com  com         ("_;;/ _"  [60, 61] 60)
      | If     bexp com com     ("(IF _/ THEN _/ ELSE _)"  [0, 0, 61] 61)
      | While  bexp com         ("(WHILE _/ DO _)"  [0, 61] 61)
(* begin mod *)
      | Or     com  com         ("_ OR/ _" [60, 61] 60)
(* end mod *)

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
\<Longrightarrow> (WHILE b DO c, s\<^sub>1) \<Rightarrow> s\<^sub>3" |
(* begin mod *)
Or1: "(c\<^sub>1, s) \<Rightarrow> t \<Longrightarrow> (c\<^sub>1 OR c\<^sub>2, s) \<Rightarrow> t" |
Or2: "(c\<^sub>2, s) \<Rightarrow> t \<Longrightarrow> (c\<^sub>1 OR c\<^sub>2, s) \<Rightarrow> t"
(* end mod *)
text_raw{*}%endsnip*}

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

(* begin mod *)
inductive_cases OrE[elim]: "(c1 OR c2, s) \<Rightarrow> t"
thm OrE
(* end mod *)

inductive_cases WhileE[elim]: "(WHILE b DO c,s) \<Rightarrow> t"
thm WhileE
text{* Only [elim]: [elim!] would not terminate. *}

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

type_synonym assn = "state \<Rightarrow> bool"

definition
hoare_valid :: "assn \<Rightarrow> com \<Rightarrow> assn \<Rightarrow> bool" ("\<Turnstile> {(1_)}/ (_)/ {(1_)}" 50) where
"\<Turnstile> {P}c{Q} = (\<forall>s t. P s \<and> (c,s) \<Rightarrow> t  \<longrightarrow>  Q t)"

abbreviation state_subst :: "state \<Rightarrow> aexp \<Rightarrow> vname \<Rightarrow> state"
  ("_[_'/_]" [1000,0,0] 999)
where "s[a/x] == s(x := aval a s)"

inductive
  hoare :: "assn \<Rightarrow> com \<Rightarrow> assn \<Rightarrow> bool" ("\<turnstile> ({(1_)}/ (_)/ {(1_)})" 50)
where
Skip: "\<turnstile> {P} SKIP {P}"  |

Assign:  "\<turnstile> {\<lambda>s. P(s[a/x])} x::=a {P}"  |

Seq: "\<lbrakk> \<turnstile> {P} c\<^sub>1 {Q};  \<turnstile> {Q} c\<^sub>2 {R} \<rbrakk>
      \<Longrightarrow> \<turnstile> {P} c\<^sub>1;;c\<^sub>2 {R}"  |

If: "\<lbrakk> \<turnstile> {\<lambda>s. P s \<and> bval b s} c\<^sub>1 {Q};  \<turnstile> {\<lambda>s. P s \<and> \<not> bval b s} c\<^sub>2 {Q} \<rbrakk>
     \<Longrightarrow> \<turnstile> {P} IF b THEN c\<^sub>1 ELSE c\<^sub>2 {Q}"  |

While: "\<turnstile> {\<lambda>s. P s \<and> bval b s} c {P} \<Longrightarrow>
        \<turnstile> {P} WHILE b DO c {\<lambda>s. P s \<and> \<not> bval b s}"  |

conseq: "\<lbrakk> \<forall>s. P' s \<longrightarrow> P s;  \<turnstile> {P} c {Q};  \<forall>s. Q s \<longrightarrow> Q' s \<rbrakk>
        \<Longrightarrow> \<turnstile> {P'} c {Q'}" |

(* begin mod *)
Or: "\<lbrakk> \<turnstile> {P} c\<^sub>1 {Q};  \<turnstile> {P} c\<^sub>2 {Q} \<rbrakk>
      \<Longrightarrow> \<turnstile> {P} c\<^sub>1 OR c\<^sub>2 {Q}"
(* end mod *)

lemmas [simp] = hoare.Skip hoare.Assign hoare.Seq If

lemmas [intro!] = hoare.Skip hoare.Assign hoare.Seq hoare.If


lemma strengthen_pre:
  "\<lbrakk> \<forall>s. P' s \<longrightarrow> P s;  \<turnstile> {P} c {Q} \<rbrakk> \<Longrightarrow> \<turnstile> {P'} c {Q}"
by (blast intro: conseq)

lemma weaken_post:
  "\<lbrakk> \<turnstile> {P} c {Q};  \<forall>s. Q s \<longrightarrow> Q' s \<rbrakk> \<Longrightarrow>  \<turnstile> {P} c {Q'}"
by (blast intro: conseq)

text{* The assignment and While rule are awkward to use in actual proofs
because their pre and postcondition are of a very special form and the actual
goal would have to match this form exactly. Therefore we derive two variants
with arbitrary pre and postconditions. *}

lemma Assign': "\<forall>s. P s \<longrightarrow> Q(s[a/x]) \<Longrightarrow> \<turnstile> {P} x ::= a {Q}"
by (simp add: strengthen_pre[OF _ Assign])

lemma While':
assumes "\<turnstile> {\<lambda>s. P s \<and> bval b s} c {P}" and "\<forall>s. P s \<and> \<not> bval b s \<longrightarrow> Q s"
shows "\<turnstile> {P} WHILE b DO c {Q}"
by(rule weaken_post[OF While[OF assms(1)] assms(2)])

subsection "Soundness"

lemma hoare_sound: "\<turnstile> {P}c{Q}  \<Longrightarrow>  \<Turnstile> {P}c{Q}"
proof(induction rule: hoare.induct)
  case (While P b c)
  { fix s t
    have "(WHILE b DO c,s) \<Rightarrow> t  \<Longrightarrow>  P s  \<Longrightarrow>  P t \<and> \<not> bval b t"
    proof(induction "WHILE b DO c" s t rule: big_step_induct)
      case WhileFalse thus ?case by blast
    next
      case WhileTrue thus ?case
        using While.IH unfolding hoare_valid_def by blast
    qed
  }
  thus ?case unfolding hoare_valid_def by blast
qed (auto simp: hoare_valid_def)


subsection "Weakest Precondition"

definition wp :: "com \<Rightarrow> assn \<Rightarrow> assn" where
"wp c Q = (\<lambda>s. \<forall>t. (c,s) \<Rightarrow> t  \<longrightarrow>  Q t)"

lemma wp_SKIP[simp]: "wp SKIP Q = Q"
by (rule ext) (auto simp: wp_def)

lemma wp_Ass[simp]: "wp (x::=a) Q = (\<lambda>s. Q(s[a/x]))"
by (rule ext) (auto simp: wp_def)

lemma wp_Seq[simp]: "wp (c\<^sub>1;;c\<^sub>2) Q = wp c\<^sub>1 (wp c\<^sub>2 Q)"
by (rule ext) (auto simp: wp_def)

lemma wp_If[simp]:
 "wp (IF b THEN c\<^sub>1 ELSE c\<^sub>2) Q =
 (\<lambda>s. if bval b s then wp c\<^sub>1 Q s else wp c\<^sub>2 Q s)"
by (rule ext) (auto simp: wp_def)

lemma wp_While_If:
 "wp (WHILE b DO c) Q s =
  wp (IF b THEN c;;WHILE b DO c ELSE SKIP) Q s"
unfolding wp_def by (metis unfold_while)

lemma wp_While_True[simp]: "bval b s \<Longrightarrow>
  wp (WHILE b DO c) Q s = wp (c;; WHILE b DO c) Q s"
by(simp add: wp_While_If)

lemma wp_While_False[simp]: "\<not> bval b s \<Longrightarrow> wp (WHILE b DO c) Q s = Q s"
by(simp add: wp_While_If)

lemma wp_Or: "wp (c1 OR c2) Q s = (wp c1 Q s \<and> wp c2 Q s)"
unfolding wp_def
by auto

subsection "Completeness"

lemma wp_is_pre: "\<turnstile> {wp c Q} c {Q}"
proof(induction c arbitrary: Q)
  case If thus ?case by(auto intro: conseq)
next
  case (While b c)
  let ?w = "WHILE b DO c"
  show "\<turnstile> {wp ?w Q} ?w {Q}"
  proof(rule While')
    show "\<turnstile> {\<lambda>s. wp ?w Q s \<and> bval b s} c {wp ?w Q}"
    proof(rule strengthen_pre[OF _ While.IH])
      show "\<forall>s. wp ?w Q s \<and> bval b s \<longrightarrow> wp c (wp ?w Q) s" by auto
    qed
    show "\<forall>s. wp ?w Q s \<and> \<not> bval b s \<longrightarrow> Q s" by auto
  qed
next
(* begin mod *)
  case (Or c1 c2)
  from this and wp_Or and big_step.Or1 and big_step.Or2
  show ?case unfolding wp_def sorry
(* end mod *)
qed auto 

lemma hoare_complete: assumes "\<Turnstile> {P}c{Q}" shows "\<turnstile> {P}c{Q}"
proof(rule strengthen_pre)
  show "\<forall>s. P s \<longrightarrow> wp c Q s" using assms
    by (auto simp: hoare_valid_def wp_def)
  show "\<turnstile> {wp c Q} c {Q}" by(rule wp_is_pre)
qed

corollary hoare_sound_complete: "\<turnstile> {P}c{Q} \<longleftrightarrow> \<Turnstile> {P}c{Q}"
by (metis hoare_complete hoare_sound)

end
