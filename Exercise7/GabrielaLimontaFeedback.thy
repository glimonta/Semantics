theory GabrielaLimonta
imports "~~/src/HOL/IMP/Star" Complex_Main
begin

(** Score: 2/5
  spec error in taval. apreservation not shown.

*)

text {* We build on @{theory Complex_Main} instead of @{theory Main} to access
the real numbers. *}

subsection "Arithmetic Expressions"

type_synonym val = real

type_synonym vname = string
type_synonym state = "vname \<Rightarrow> val"

text_raw{*\snip{aexptDef}{0}{2}{% *}
datatype aexp = Rc real | V vname | Plus aexp aexp | Div aexp aexp
text_raw{*}%endsnip*}

inductive taval :: "aexp \<Rightarrow> state \<Rightarrow> val \<Rightarrow> bool" where
"taval (Rc r) s r" |
"taval (V x) s (s x)" |
"taval a1 s r1 \<Longrightarrow> taval a2 s r2
  \<Longrightarrow> taval (Plus a1 a2) s (r1+r2)" |
"taval a1 s r1 \<Longrightarrow> taval a2 s r2        (** No, should get stuck on div by zero!*)
  \<Longrightarrow> taval (Div a1 a2) s (r1 / r2)" 

inductive_cases [elim!]:
  "taval (Rc i) s v"
  "taval (V x) s v"
  "taval (Plus a1 a2) s v"
  "taval (Div a1 a2) s v"

subsection "Boolean Expressions"

datatype bexp = Bc bool | Not bexp | And bexp bexp | Less aexp aexp

inductive tbval :: "bexp \<Rightarrow> state \<Rightarrow> bool \<Rightarrow> bool" where
"tbval (Bc v) s v" |
"tbval b s bv \<Longrightarrow> tbval (Not b) s (\<not> bv)" |
"tbval b1 s bv1 \<Longrightarrow> tbval b2 s bv2 \<Longrightarrow> tbval (And b1 b2) s (bv1 & bv2)" |
"taval a1 s r1 \<Longrightarrow> taval a2 s r2 \<Longrightarrow> tbval (Less a1 a2) s (r1 < r2)"

subsection "Syntax of Commands"
(* a copy of Com.thy - keep in sync! *)

datatype
  com = SKIP 
      | Assign vname aexp       ("_ ::= _" [1000, 61] 61)
      | Seq    com  com         ("_;; _"  [60, 61] 60)
      | If     bexp com com     ("IF _ THEN _ ELSE _"  [0, 0, 61] 61)
      | While  bexp com         ("WHILE _ DO _"  [0, 61] 61)


subsection "Small-Step Semantics of Commands"

inductive
  small_step :: "(com \<times> state) \<Rightarrow> (com \<times> state) \<Rightarrow> bool" (infix "\<rightarrow>" 55)
where
Assign:  "taval a s v \<Longrightarrow> (x ::= a, s) \<rightarrow> (SKIP, s(x := v))" |

Seq1:   "(SKIP;;c,s) \<rightarrow> (c,s)" |
Seq2:   "(c1,s) \<rightarrow> (c1',s') \<Longrightarrow> (c1;;c2,s) \<rightarrow> (c1';;c2,s')" |

IfTrue:  "tbval b s True \<Longrightarrow> (IF b THEN c1 ELSE c2,s) \<rightarrow> (c1,s)" |
IfFalse: "tbval b s False \<Longrightarrow> (IF b THEN c1 ELSE c2,s) \<rightarrow> (c2,s)" |

While:   "(WHILE b DO c,s) \<rightarrow> (IF b THEN c;; WHILE b DO c ELSE SKIP,s)"

lemmas small_step_induct = small_step.induct[split_format(complete)]

subsection "The Type System"

datatype ty = Neg | Pos | Zero | Any

definition ty_of_c :: "real \<Rightarrow> ty" where
  "ty_of_c r = (if r = 0 then Zero else (if r > 0 then Pos else Neg))"

fun ty_of_plus :: "ty \<Rightarrow> ty \<Rightarrow> ty" where
  "ty_of_plus Neg Neg = Neg" |
  "ty_of_plus Pos Pos = Pos" |
  "ty_of_plus Neg Pos = Any" |
  "ty_of_plus Pos Neg = Any" |
  "ty_of_plus Any _ = Any" |
  "ty_of_plus _ Any = Any" |
  "ty_of_plus Zero a = a" |
  "ty_of_plus a Zero = a"

fun ty_of_div :: "ty \<Rightarrow> ty \<Rightarrow> ty option" where
  "ty_of_div Neg Neg = Some Pos" |
  "ty_of_div Pos Pos = Some Pos" |
  "ty_of_div Neg Pos = Some Neg" |
  "ty_of_div Pos Neg = Some Neg" |
  "ty_of_div a Zero = None" |
  "ty_of_div Zero a = Some Zero" |
  "ty_of_div Any Pos = Some Any" |
  "ty_of_div Any Neg = Some Any" |
  "ty_of_div _ Any = None"

type_synonym tyenv = "vname \<Rightarrow> ty"

inductive atyping :: "tyenv \<Rightarrow> aexp \<Rightarrow> ty \<Rightarrow> bool"
  ("(1_/ \<turnstile>/ (_ :/ _))" [50,0,50] 50)
where
Rc_ty: "\<Gamma> \<turnstile> Rc r : ty_of_c r" |
V_ty: "\<Gamma> \<turnstile> V x : \<Gamma> x" |
Plus_ty: "\<Gamma> \<turnstile> a1 : \<tau>1 \<Longrightarrow> \<Gamma> \<turnstile> a2 : \<tau>2 \<Longrightarrow>  \<Gamma> \<turnstile> Plus a1 a2 : ty_of_plus \<tau>1 \<tau>2" |
Div_ty: "\<Gamma> \<turnstile> a1 : \<tau>1 \<Longrightarrow> \<Gamma> \<turnstile> a2 : \<tau>2 \<Longrightarrow> ty_of_div \<tau>1 \<tau>2 = Some \<tau> \<Longrightarrow> \<Gamma> \<turnstile> Div a1 a2 : \<tau>"

fun values_of_type :: "ty \<Rightarrow> real set" where
  "values_of_type Neg = {x. x<0}" |
  "values_of_type Pos = {x. x>0}" |
  "values_of_type Zero = {0}" |
  "values_of_type Any = {x. x<0 \<or> x\<ge>0}"  (** The universal set is UNIV *)

lemma "({x. x<0 \<or> x\<ge>0}::real set) = UNIV" by auto (** Much more concise to write ;) *)


declare atyping.intros [intro!]
inductive_cases [elim!]:
  "\<Gamma> \<turnstile> V x : \<tau>" "\<Gamma> \<turnstile> Rc r : \<tau>" "\<Gamma> \<turnstile> Plus a1 a2 : \<tau>" "\<Gamma> \<turnstile> Div a1 a2 : \<tau>"

text{* Warning: the ``:'' notation leads to syntactic ambiguities,
i.e. multiple parse trees, because ``:'' also stands for set membership.
In most situations Isabelle's type system will reject all but one parse tree,
but will still inform you of the potential ambiguity. *}

inductive btyping :: "tyenv \<Rightarrow> bexp \<Rightarrow> bool" (infix "\<turnstile>" 50)
where
B_ty: "\<Gamma> \<turnstile> Bc v" |
Not_ty: "\<Gamma> \<turnstile> b \<Longrightarrow> \<Gamma> \<turnstile> Not b" |
And_ty: "\<Gamma> \<turnstile> b1 \<Longrightarrow> \<Gamma> \<turnstile> b2 \<Longrightarrow> \<Gamma> \<turnstile> And b1 b2" |
Less_ty: "\<Gamma> \<turnstile> a1 : \<tau> \<Longrightarrow> \<Gamma> \<turnstile> a2 : \<tau> \<Longrightarrow> \<Gamma> \<turnstile> Less a1 a2"

declare btyping.intros [intro!]
inductive_cases [elim!]: "\<Gamma> \<turnstile> Not b" "\<Gamma> \<turnstile> And b1 b2" "\<Gamma> \<turnstile> Less a1 a2"

inductive ctyping :: "tyenv \<Rightarrow> com \<Rightarrow> bool" (infix "\<turnstile>" 50) where
Skip_ty: "\<Gamma> \<turnstile> SKIP" |
Assign_ty: "\<Gamma> \<turnstile> a : \<Gamma>(x) \<Longrightarrow> \<Gamma> \<turnstile> x ::= a" |
Seq_ty: "\<Gamma> \<turnstile> c1 \<Longrightarrow> \<Gamma> \<turnstile> c2 \<Longrightarrow> \<Gamma> \<turnstile> c1;;c2" |
If_ty: "\<Gamma> \<turnstile> b \<Longrightarrow> \<Gamma> \<turnstile> c1 \<Longrightarrow> \<Gamma> \<turnstile> c2 \<Longrightarrow> \<Gamma> \<turnstile> IF b THEN c1 ELSE c2" |
While_ty: "\<Gamma> \<turnstile> b \<Longrightarrow> \<Gamma> \<turnstile> c \<Longrightarrow> \<Gamma> \<turnstile> WHILE b DO c"

declare ctyping.intros [intro!]
inductive_cases [elim!]:
  "\<Gamma> \<turnstile> x ::= a"  "\<Gamma> \<turnstile> c1;;c2"
  "\<Gamma> \<turnstile> IF b THEN c1 ELSE c2"
  "\<Gamma> \<turnstile> WHILE b DO c"

subsection "Well-typed Programs Do Not Get Stuck"
(*
fun type :: "val \<Rightarrow> ty" where
"type (Iv i) = Ity" |
"type (Rv r) = Rty"


lemma type_eq_Rty[simp]: "type v = Rty \<longleftrightarrow> (\<exists>r. v = Rv r)"
by (cases v) simp_all
*)

definition styping :: "tyenv \<Rightarrow> state \<Rightarrow> bool" (infix "\<turnstile>" 50)
where "\<Gamma> \<turnstile> s  \<longleftrightarrow>  (\<forall>x. s x \<in> values_of_type (\<Gamma> x))"

lemma apreservation:
  "\<Gamma> \<turnstile> a : \<tau> \<Longrightarrow> taval a s v \<Longrightarrow> \<Gamma> \<turnstile> s \<Longrightarrow> v \<in> (values_of_type \<tau>)"
proof (induction arbitrary: v rule: atyping.induct)
  print_cases
  case (Rc_ty \<Gamma> r)
    thus ?case using ty_of_c_def by fastforce
  next
  case (V_ty \<Gamma> x)
    thus ?case
    proof -
      have "s x = v" using V_ty.prems(1) by force
      thus "v \<in> values_of_type   (\<Gamma> x)" using V_ty.prems(2) styping_def by blast
    qed
  next
  case (Plus_ty \<Gamma> a1 \<tau>1 a2 \<tau>2)
    thus ?case sorry
  next
  case (Div_ty \<Gamma> a1 \<tau>1 a2 \<tau>2 \<tau>)
    thus ?case using taval.intros(4)[of a1 s r1 a2 r2] sorry
qed

(*
apply(induction arbitrary: v rule: atyping.induct)
apply (fastforce simp: styping_def)+ 
done*)


lemma aprogress: "\<Gamma> \<turnstile> a : \<tau> \<Longrightarrow> \<Gamma> \<turnstile> s \<Longrightarrow> \<exists>v. taval a s v"
proof(induction rule: atyping.induct)
  print_cases
  case (Plus_ty \<Gamma> a1 \<tau>1 a2 \<tau>2)
  then obtain v1 v2 where v: "taval a1 s v1" "taval a2 s v2" by blast
  show ?case using Plus_ty taval.intros by blast
qed (auto intro: taval.intros)

lemma bprogress: "\<Gamma> \<turnstile> b \<Longrightarrow> \<Gamma> \<turnstile> s \<Longrightarrow> \<exists>v. tbval b s v"
proof(induction rule: btyping.induct)
print_cases
  case (Less_ty \<Gamma> a1 t a2)
  then obtain v1 v2 where v: "taval a1 s v1" "taval a2 s v2"
    by (metis aprogress)
  show ?case using tbval.intros v(1) v(2) by blast
qed (auto intro: tbval.intros)

theorem progress:
  "\<Gamma> \<turnstile> c \<Longrightarrow> \<Gamma> \<turnstile> s \<Longrightarrow> c \<noteq> SKIP \<Longrightarrow> \<exists>cs'. (c,s) \<rightarrow> cs'"
proof(induction rule: ctyping.induct)
  case Skip_ty thus ?case by simp
next
  case Assign_ty 
  thus ?case by (metis Assign aprogress)
next
  case Seq_ty thus ?case by simp (metis Seq1 Seq2)
next
  case (If_ty \<Gamma> b c1 c2)
  then obtain bv where "tbval b s bv" by (metis bprogress)
  show ?case
  proof(cases bv)
    assume "bv"
    with `tbval b s bv` show ?case by simp (metis IfTrue)
  next
    assume "\<not>bv"
    with `tbval b s bv` show ?case by simp (metis IfFalse)
  qed
next
  case While_ty show ?case by (metis While)
qed

theorem styping_preservation:
  "(c,s) \<rightarrow> (c',s') \<Longrightarrow> \<Gamma> \<turnstile> c \<Longrightarrow> \<Gamma> \<turnstile> s \<Longrightarrow> \<Gamma> \<turnstile> s'"
proof(induction rule: small_step_induct)
  case Assign thus ?case
    by (auto simp: styping_def) (metis Assign(1,3) apreservation)
qed auto

theorem ctyping_preservation:
  "(c,s) \<rightarrow> (c',s') \<Longrightarrow> \<Gamma> \<turnstile> c \<Longrightarrow> \<Gamma> \<turnstile> c'"
by (induct rule: small_step_induct) (auto simp: ctyping.intros)

abbreviation small_steps :: "com * state \<Rightarrow> com * state \<Rightarrow> bool" (infix "\<rightarrow>*" 55)
where "x \<rightarrow>* y == star small_step x y"

theorem type_sound:
  "(c,s) \<rightarrow>* (c',s') \<Longrightarrow> \<Gamma> \<turnstile> c \<Longrightarrow> \<Gamma> \<turnstile> s \<Longrightarrow> c' \<noteq> SKIP
   \<Longrightarrow> \<exists>cs''. (c',s') \<rightarrow> cs''"
apply(induction rule:star_induct)
apply (metis progress)
by (metis styping_preservation ctyping_preservation)

end
