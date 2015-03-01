(*<*)
theory sol04
imports "~~/src/HOL/IMP/BExp" "~~/src/HOL/IMP/ASM"
begin
(*>*)
text {* \ExerciseSheet{4}{4.~11.~2014} *}

text {* \Exercise{Reflexive Transitive Closure}
A binary relation is expressed by a predicate of type
  @{text "R :: 's \<Rightarrow> 's \<Rightarrow> bool"}. Intuitively, @{text "R s t"} represents
  a single step from state @{text "s"} to state @{text "t"}.

The reflexive, transitive closure @{text "R\<^sup>*"} of @{text "R"} is the relation 
  that contains a step @{text "R\<^sup>* s t"}, iff @{text "R"} can step 
  from @{text "s"} to @{text "t"} in any number of steps (including zero steps).

Formalize the reflexive transitive closure as inductive predicate:
*}

inductive star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
(*<*)
  for r where
  refl:  "star r x x" |
  step:  "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"
(*>*)

text {* When doing so, you have the choice to append or prepend a step.
  In any case, the following two lemmas should hold for your definition: *}

lemma star_prepend: "\<lbrakk>r x y; star r y z\<rbrakk> \<Longrightarrow> star r x z" 
(*<*)
  by (rule step)
(*>*)

lemma star_append: "\<lbrakk> star r x y; r y z \<rbrakk> \<Longrightarrow> star r x z"
(*<*)
  by (induct rule: star.induct) (auto intro: star.intros)
(*>*)

text {* Now, formalize the star predicate again, this time the other way 
  round: *}
inductive star' :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
(*<*)
  for r where
  refl': "star' r x x" |
  step': "\<lbrakk>star' r x y; r y z\<rbrakk> \<Longrightarrow> star' r x z"
(*>*)

(*<*)
lemma star'_prepend:
  "\<lbrakk>star' r y z; r x y\<rbrakk> \<Longrightarrow> star' r x z"
  apply (induction rule: star'.induct)
  apply (auto intro: star'.intros)
  done
(*>*)

text {* Prove the equivalence of your two formalizations *}
lemma "star r x y = star' r x y"
(*<*)
proof
  assume "star r x y"
  thus "star' r x y"
    by induct (auto intro: star'.intros star'_prepend)
next
  assume "star' r x y"
  thus "star r x y"
    by induct (auto intro: star.intros star_append)
qed
(*>*)

text {*
  Hint: The induction method expects the assumption about the inductive
  predicate to be first.
*}


text {*\Exercise{Elements of a List} *}
text {* {\bf Give all your proofs in Isar, not apply style}*}

text {*

Define a recursive function @{text "elems"} returning the set of elements of a list:

*}

fun elems :: "'a list \<Rightarrow> 'a set" 
(*<*)
where
  "elems [] = {}"
| "elems (x#xs) = {x} \<union> elems xs"
(*>*)

text {* To test your definition, prove: *}
lemma "elems [1,2,3,(4::nat)] = {1,2,3,4}" (*<*)by auto(*>*)

text {*

Now prove for each element @{term x} in a list @{term xs} that we can split @{term xs} in a prefix
not containing @{term x}, @{term x} itself and a rest:

*}

lemma "x \<in> elems xs \<Longrightarrow> \<exists>ys zs. xs = ys @ x # zs \<and> x \<notin> elems ys"
(*<*)
proof (induction xs)
  case Nil
  then show ?case
    by simp
next
  case (Cons y xs)
  show ?case
  proof cases
    assume eq: "x = y"
    show ?thesis
    proof (* \<exists>-introduction *)
      show "\<exists>zs. y # xs = [] @ x # zs \<and> x \<notin> elems []"
        using eq by simp
    qed
  next
    assume neq: "x \<noteq> y"
    with Cons obtain ys zs where ys: "xs = ys @ x # zs" "x \<notin> elems ys"
      by auto
    show ?thesis
    proof (* \<exists>-introduction *)
      show "\<exists>zs. y # xs = (y # ys) @ x # zs \<and> x \<notin> elems (y # ys)"
        using ys neq by simp
    qed
  qed
qed
(*>*)



text {* \Exercise{Rule Inversion}
Recall the evenness predicate @{text "ev"} from the lecture: *}

inductive ev :: "nat \<Rightarrow> bool" where
  ev0: "ev 0" |
  evSS: "ev n \<Longrightarrow> ev (Suc (Suc n))"

text {* Prove the converse of rule @{text "evSS"} using rule
inversion. Hint: There are two ways to proceed. First, you can write a
structured Isar-style proof using the @{text "cases"} method: *}

lemma "ev (Suc (Suc n)) \<Longrightarrow> ev n"
proof -
  assume "ev (Suc (Suc n))" then show "ev n" by cases
qed

text {* Alternatively, you can write a more automated proof by using
the elimination rules.
These rules can then be used with ``@{text "auto elim:"}''. (If given
the @{text "[elim]"} attribute, @{text "auto"} will use them by
default.) *}

(*<*)
lemma "ev (Suc (Suc n)) \<Longrightarrow> ev n" by (auto elim: ev.cases)
(*>*)

text {* Next, prove that the natural number three (@{text "Suc (Suc
(Suc 0))"}) is not even. Hint: You may proceed either with a
structured proof, or with an automatic one. An automatic proof may
require additional elimination rules from \textbf{inductive\_cases}.
*}

lemma "\<not> ev (Suc (Suc (Suc 0)))"
(*<*)
proof
  assume "ev (Suc (Suc (Suc 0)))" then show "False"
  proof (cases)
    assume "ev (Suc 0)" then show "False"
    proof (cases)
    qed
  qed
qed
lemma "\<not> ev (Suc (Suc (Suc 0)))"
  by (auto elim: ev.cases)
(*>*)

(*<*)
end
(*>*)
