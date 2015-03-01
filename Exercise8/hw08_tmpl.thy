header "A Typed Language"

theory hw08_tmpl imports "~~/src/HOL/IMP/Star" begin

subsection "Expressions"

datatype val = Iv int | Bv bool

type_synonym vname = string
type_synonym state = "vname \<Rightarrow> val"

datatype exp =  N int | V vname | Plus exp exp |
  Bc bool | Not exp | And exp exp | Less exp exp

inductive eval :: "exp \<Rightarrow> state \<Rightarrow> val \<Rightarrow> bool" where
"eval (N i) s (Iv i)" |
"eval (V x) s (s x)" |
"eval a1 s (Iv i1) \<Longrightarrow> eval a2 s (Iv i2)
 \<Longrightarrow> eval (Plus a1 a2) s (Iv(i1+i2))" |
"eval (Bc v) s (Bv v)" |
"eval b s (Bv bv) \<Longrightarrow> eval (Not b) s (Bv(\<not> bv))" |
"eval b1 s (Bv bv1) \<Longrightarrow> eval b2 s (Bv bv2) \<Longrightarrow> eval (And b1 b2) s (Bv(bv1 & bv2))" |
"eval a1 s (Iv i1) \<Longrightarrow> eval a2 s (Iv i2) \<Longrightarrow> eval (Less a1 a2) s (Bv(i1 < i2))"

inductive_cases [elim!]:
  "eval (N i) s v"
  "eval (V x) s v"
  "eval (Plus a1 a2) s v"
  "eval (Bc b) s v"
  "eval (Not b) s v"
  "eval (And b1 b2) s v"
  "eval (Less a1 a2) s v"

subsection "Syntax of Commands"
(* a copy of Com.thy - keep in sync! *)

datatype
  com = SKIP 
      | Assign vname exp       ("_ ::= _" [1000, 61] 61)
      | Seq    com  com         ("_;; _"  [60, 61] 60)
      | If     exp com com     ("IF _ THEN _ ELSE _"  [0, 0, 61] 61)
      | While  exp com         ("WHILE _ DO _"  [0, 61] 61)


subsection "Small-Step Semantics of Commands"

inductive
  small_step :: "(com \<times> state) \<Rightarrow> (com \<times> state) \<Rightarrow> bool" (infix "\<rightarrow>" 55)
where
Assign:  "eval a s v \<Longrightarrow> (x ::= a, s) \<rightarrow> (SKIP, s(x := v))" |

Seq1:   "(SKIP;;c,s) \<rightarrow> (c,s)" |
Seq2:   "(c1,s) \<rightarrow> (c1',s') \<Longrightarrow> (c1;;c2,s) \<rightarrow> (c1';;c2,s')" |

IfTrue:  "eval b s (Bv True) \<Longrightarrow> (IF b THEN c1 ELSE c2,s) \<rightarrow> (c1,s)" |
IfFalse: "eval b s (Bv False) \<Longrightarrow> (IF b THEN c1 ELSE c2,s) \<rightarrow> (c2,s)" |

While:   "(WHILE b DO c,s) \<rightarrow> (IF b THEN c;; WHILE b DO c ELSE SKIP,s)"

lemmas small_step_induct = small_step.induct[split_format(complete)]

subsection "The Type System"

datatype ty = Ity | Bty

type_synonym tyenv = "vname \<Rightarrow> ty"

inductive etyping :: "tyenv \<Rightarrow> exp \<Rightarrow> ty \<Rightarrow> bool"
  ("(1_/ \<turnstile>/ (_ :/ _))" [50,0,50] 50)
where
Ic_ty: "\<Gamma> \<turnstile> N i : Ity" |
V_ty: "\<Gamma> \<turnstile> V x : \<Gamma> x" |
Plus_ty: "\<Gamma> \<turnstile> a1 : Ity \<Longrightarrow> \<Gamma> \<turnstile> a2 : Ity \<Longrightarrow> \<Gamma> \<turnstile> Plus a1 a2 : Ity" |
B_ty: "\<Gamma> \<turnstile> Bc v : Bty" |
Not_ty: "\<Gamma> \<turnstile> b : Bty \<Longrightarrow> \<Gamma> \<turnstile> Not b : Bty" |
And_ty: "\<Gamma> \<turnstile> b1 : Bty \<Longrightarrow> \<Gamma> \<turnstile> b2 : Bty \<Longrightarrow> \<Gamma> \<turnstile> And b1 b2 : Bty" |
Less_ty: "\<Gamma> \<turnstile> a1 : Ity \<Longrightarrow> \<Gamma> \<turnstile> a2 : Ity \<Longrightarrow> \<Gamma> \<turnstile> Less a1 a2 : Bty"

inductive ctyping :: "tyenv \<Rightarrow> com \<Rightarrow> bool" (infix "\<turnstile>" 50) where
Skip_ty: "\<Gamma> \<turnstile> SKIP" |
Assign_ty: "\<Gamma> \<turnstile> a : \<Gamma>(x) \<Longrightarrow> \<Gamma> \<turnstile> x ::= a" |
Seq_ty: "\<Gamma> \<turnstile> c1 \<Longrightarrow> \<Gamma> \<turnstile> c2 \<Longrightarrow> \<Gamma> \<turnstile> c1;;c2" |
If_ty: "\<Gamma> \<turnstile> b : Bty \<Longrightarrow> \<Gamma> \<turnstile> c1 \<Longrightarrow> \<Gamma> \<turnstile> c2 \<Longrightarrow> \<Gamma> \<turnstile> IF b THEN c1 ELSE c2" |
While_ty: "\<Gamma> \<turnstile> b : Bty \<Longrightarrow> \<Gamma> \<turnstile> c \<Longrightarrow> \<Gamma> \<turnstile> WHILE b DO c"

inductive_cases [elim!]:
  "\<Gamma> \<turnstile> x ::= a"  "\<Gamma> \<turnstile> c1;;c2"
  "\<Gamma> \<turnstile> IF b THEN c1 ELSE c2"
  "\<Gamma> \<turnstile> WHILE b DO c"

subsection "Well-typed Programs Do Not Get Stuck"

fun type :: "val \<Rightarrow> ty" where
"type (Iv i) = Ity" |
"type (Bv r) = Bty"

lemma type_eq_Ity[simp]: "type v = Ity \<longleftrightarrow> (\<exists>i. v = Iv i)"
by (cases v) simp_all

lemma type_eq_Bty[simp]: "type v = Bty \<longleftrightarrow> (\<exists>r. v = Bv r)"
by (cases v) simp_all

definition styping :: "tyenv \<Rightarrow> state \<Rightarrow> bool" (infix "\<turnstile>" 50)
where "\<Gamma> \<turnstile> s  \<longleftrightarrow>  (\<forall>x. type (s x) = \<Gamma> x)"

lemma epreservation:
  "\<Gamma> \<turnstile> a : \<tau> \<Longrightarrow> eval a s v \<Longrightarrow> \<Gamma> \<turnstile> s \<Longrightarrow> type v = \<tau>"
oops

lemma eprogress: "\<Gamma> \<turnstile> a : \<tau> \<Longrightarrow> \<Gamma> \<turnstile> s \<Longrightarrow> \<exists>v. eval a s v"
oops

theorem progress:
  "\<Gamma> \<turnstile> c \<Longrightarrow> \<Gamma> \<turnstile> s \<Longrightarrow> c \<noteq> SKIP \<Longrightarrow> \<exists>cs'. (c,s) \<rightarrow> cs'"
oops

theorem styping_preservation:
  "(c,s) \<rightarrow> (c',s') \<Longrightarrow> \<Gamma> \<turnstile> c \<Longrightarrow> \<Gamma> \<turnstile> s \<Longrightarrow> \<Gamma> \<turnstile> s'"
oops

theorem ctyping_preservation:
  "(c,s) \<rightarrow> (c',s') \<Longrightarrow> \<Gamma> \<turnstile> c \<Longrightarrow> \<Gamma> \<turnstile> c'"
oops

abbreviation small_steps :: "com * state \<Rightarrow> com * state \<Rightarrow> bool" (infix "\<rightarrow>*" 55)
where "x \<rightarrow>* y == star small_step x y"

theorem type_sound:
  "(c,s) \<rightarrow>* (c',s') \<Longrightarrow> \<Gamma> \<turnstile> c \<Longrightarrow> \<Gamma> \<turnstile> s \<Longrightarrow> c' \<noteq> SKIP
   \<Longrightarrow> \<exists>cs''. (c',s') \<rightarrow> cs''"
oops

end
