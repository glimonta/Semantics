theory Ex08
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
  "\<lbrakk> sec b \<le> l;  \<turnstile>' c\<^sub>1 : l;  \<turnstile>' c\<^sub>2 : l \<rbrakk>
  \<Longrightarrow> \<turnstile>' IF b THEN c\<^sub>1 ELSE c\<^sub>2 : l" |
While2':
  "\<lbrakk> sec b \<le> l;  \<turnstile>' c : l \<rbrakk> \<Longrightarrow> \<turnstile>' WHILE b DO c : l" |
Subsumption2':
  "\<lbrakk> \<turnstile>' c : l; l' \<le> l \<rbrakk> \<Longrightarrow> \<turnstile>' c : l'"


lemma
  assumes "\<turnstile> c : l"
  shows "\<turnstile>' c : l"
  using assms
  apply (induction)
  apply (auto intro: sec_type2'.intros)
  apply (metis Semi2' Subsumption2' min.cobounded1 min.cobounded2)
  by (metis If2' Subsumption2' min.cobounded2 min.commute min_def)

lemma "\<turnstile>' c : l \<Longrightarrow> \<exists>l' \<ge> l. \<turnstile> c : l'"
  apply(induction rule: sec_type2'.induct)
  apply(force intro: sec_type2.intros)
  apply (metis Assign2 order_refl)
  apply (metis Seq2 inf_greatest inf_nat_def)
  apply (metis If2 le_trans min.boundedI)
  apply (metis While2 le_trans)
  by (metis le_trans)

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
  "AA SKIP = {}" |
  "AA (x ::= a) = {x}" |
  "AA (c1;;c2) = AA c1 \<union> AA c2" |
  "AA (IF _ THEN c1 ELSE c2) = AA c1 \<inter> AA c2" |
  "AA (WHILE b DO c) = {}"

fun D :: "vname set \<Rightarrow> com \<Rightarrow> bool" where
  "D A SKIP = True" |
  "D A (x ::= a) \<longleftrightarrow> vars a \<subseteq> A" |
  "D A (c1;;c2) \<longleftrightarrow> D A c1 \<and> D (A \<union> AA c1) c2" |
  "D A (IF b THEN c1 ELSE c2) \<longleftrightarrow> vars b \<subseteq> A \<and> D A c1 \<and> D A c2 " |
  "D A (WHILE b DO c) \<longleftrightarrow> vars b \<subseteq> A \<and> D A c"

subsection "Soundness wrt Small Steps"

theorem progress:
"D (dom s) c \<Longrightarrow> c \<noteq> SKIP \<Longrightarrow> \<exists> cs'. (c,s) \<rightarrow> cs'"
  apply (induction c arbitrary: s)
  apply (auto intro: small_step.intros)
  apply (metis aval_Some small_step.Assign)
  apply (force intro: small_step.intros)
  by (metis (full_types) bval_Some small_step.IfFalse small_step.IfTrue)

lemma D_incr: "(c,s) \<rightarrow> (c',s') \<Longrightarrow> dom s \<union> AA c \<subseteq> dom s' \<union> AA c'"
  apply (induction rule: small_step_induct)
  by auto

lemma D_mono: "A \<subseteq> A' \<Longrightarrow> D A c \<Longrightarrow> D A' c"
  apply (induction c arbitrary: A A')
  apply (auto)
  by (metis sup.absorb2 sup.left_commute sup_assoc sup_ge2)

theorem D_preservation:
"(c,s) \<rightarrow> (c',s') \<Longrightarrow> D (dom s) c \<Longrightarrow> D (dom s') c'"
  apply (induction rule: small_step_induct)
  apply (auto)
  by (auto intro: D_mono dest: D_mono D_incr)


theorem D_sound:
"(c,s) \<rightarrow>* (c',s') \<Longrightarrow> D (dom s) c \<Longrightarrow> c' \<noteq> SKIP
 \<Longrightarrow> \<exists>cs''. (c',s') \<rightarrow> cs''"
  apply(induction rule: small_steps_induct)
  apply (metis progress)
  by (metis D_preservation)

end
