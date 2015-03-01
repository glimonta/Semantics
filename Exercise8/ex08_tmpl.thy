theory ex08_tmpl
imports
  "~~/src/HOL/IMP/Sec_Typing"
  "~~/src/HOL/IMP/Com"
  "~~/src/HOL/IMP/Def_Init_Exp"
  "~~/src/HOL/IMP/Def_Init"
  "~~/src/HOL/IMP/Vars"
begin

subsection {* Ex 08.1: Security type system: bottom-up with subsumption *}

inductive sec_type2' :: "com \<Rightarrow> level \<Rightarrow> bool" ("(\<turnstile>' _ : _)" [0,0] 50) where
Skip2':
  "\<turnstile>' SKIP : l" |
Assign2':
  "sec x \<ge> sec a \<Longrightarrow> \<turnstile>' x ::= a : sec x" |
Semi2':
  "\<lbrakk> \<turnstile>' c\<^sub>1 : l;  \<turnstile>' c\<^sub>2 : l \<rbrakk> \<Longrightarrow> \<turnstile>' c\<^sub>1 ;; c\<^sub>2 : l" |
If2':
  "\<lbrakk> sec b \<le> min l\<^sub>1 l\<^sub>2;  \<turnstile>' c\<^sub>1 : l\<^sub>1;  \<turnstile>' c\<^sub>2 : l\<^sub>2 \<rbrakk>
  \<Longrightarrow> \<turnstile>' IF b THEN c\<^sub>1 ELSE c\<^sub>2 : min l\<^sub>1 l\<^sub>2" |
While2':
  "\<lbrakk> sec b \<le> l;  \<turnstile>' c : l \<rbrakk> \<Longrightarrow> \<turnstile>' WHILE b DO c : l"


lemma "\<turnstile> c : l \<Longrightarrow> \<turnstile>' c : l"
oops


lemma "\<turnstile>' c : l \<Longrightarrow> \<exists>l' \<ge> l. \<turnstile> c : l'"
oops

section {* Ex 08.2: Initialization-Sensitive Small Step Semantics *}

inductive
  small_step :: "(com \<times> state) \<Rightarrow> (com \<times> state) \<Rightarrow> bool" (infix "\<rightarrow>" 55)
where
Assign:  "aval a s = Some i \<Longrightarrow> (x ::= a, s) \<rightarrow> (SKIP, s(x := Some i))" |

Seq1:   "(SKIP;;c,s) \<rightarrow> (c,s)" |
Seq2:   "(c\<^sub>1,s) \<rightarrow> (c\<^sub>1',s') \<Longrightarrow> (c\<^sub>1;;c\<^sub>2,s) \<rightarrow> (c\<^sub>1';;c\<^sub>2,s')" |

IfTrue:  "bval b s = Some True \<Longrightarrow> (IF b THEN c\<^sub>1 ELSE c\<^sub>2,s) \<rightarrow> (c\<^sub>1,s)" |
IfFalse: "bval b s = Some False \<Longrightarrow> (IF b THEN c\<^sub>1 ELSE c\<^sub>2,s) \<rightarrow> (c\<^sub>2,s)" |

While:   "(WHILE b DO c,s) \<rightarrow> (IF b THEN c;; WHILE b DO c ELSE SKIP,s)"

lemmas small_step_induct = small_step.induct[split_format(complete)]

inductive
  small_steps :: "com * state \<Rightarrow> com * state \<Rightarrow> bool"  (infix "\<rightarrow>*" 55)  where
refl:  "cs \<rightarrow>* cs" |
step:  "cs \<rightarrow> cs' \<Longrightarrow> cs' \<rightarrow>* cs'' \<Longrightarrow> cs \<rightarrow>* cs''"

lemmas small_steps_induct = small_steps.induct[split_format(complete)]


subsection "Definite Initialization Analysis"

fun AA :: "com \<Rightarrow> vname set" where
"AA c = undefined"   (* provide a suitable definition *)

fun D :: "vname set \<Rightarrow> com \<Rightarrow> bool" where
"D A c = undefined"   (* provide a suitable definition *)

subsection "Soundness wrt Small Steps"

theorem progress:
"D (dom s) c \<Longrightarrow> c \<noteq> SKIP \<Longrightarrow> \<exists> cs'. (c,s) \<rightarrow> cs'"
oops

lemma D_incr: "(c,s) \<rightarrow> (c',s') \<Longrightarrow> dom s \<union> AA c \<subseteq> dom s' \<union> AA c'"
oops

lemma D_mono: "A \<subseteq> A' \<Longrightarrow> D A c \<Longrightarrow> D A' c"
oops

theorem D_preservation:
"(c,s) \<rightarrow> (c',s') \<Longrightarrow> D (dom s) c \<Longrightarrow> D (dom s') c'"
oops

theorem D_sound:
"(c,s) \<rightarrow>* (c',s') \<Longrightarrow> D (dom s) c \<Longrightarrow> c' \<noteq> SKIP
 \<Longrightarrow> \<exists>cs''. (c',s') \<rightarrow> cs''"
oops


end
