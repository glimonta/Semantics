(** Score: 10/20 *)

(**
Formalized a little bit of DFAs and the Pumping Lemma. Unfortunately only one
proof, the pigeonhole principle, which requires an unproved lemma and which
is still some way removed from the Pumping Lemma itself.
*)

theory GabrielaLimonta
imports Main
begin

(* Pumping Lemma for regular languages *)

(* We start by formalizing a representation of a DFA, the states will be represented by nat numbers.
   The delta function has the type "'a \<Rightarrow> state \<Rightarrow> state".
   A DFA has the following type: "state set \<Rightarrow> state \<Rightarrow> state set \<Rightarrow> ('a \<Rightarrow> state \<Rightarrow> state)", this
   represents the states of the DFA, the initial state, the final states and the delta function. *)
type_synonym state = nat

(* the states for our DFA are identified by nat and a word is a list of nat numbers, a language
   represented by the DFA is a set of nat list *)

(* A word in a language is represented by a list. The language represented by a DFA is a set of lists.
   The function consume takes a word and indicates the state the DFA is after consuming that word. *)
fun consume :: "'a list \<Rightarrow> ('a \<Rightarrow> state \<Rightarrow> state) \<Rightarrow> state set \<Rightarrow> state \<Rightarrow> state" where
  "consume [] \<delta> Q = id" |
  "consume (a#w) \<delta> Q = consume w \<delta> Q \<circ> \<delta> a"

value "consume [] (\<lambda>x y. y+1) {0,1,2} 0"
value "consume [1,2,3] (\<lambda>x y. y+1) {0,1,2} 0"

(* The language represented by a DFA is the set of words w that allow us to go from the initial
   state to one of the final states *)
fun language :: "state set \<Rightarrow> state \<Rightarrow> state set \<Rightarrow> ('a \<Rightarrow> state \<Rightarrow> state) \<Rightarrow> 'a list set" where
  "language Q q\<^sub>0 q\<^sub>f \<delta> = {w. consume w \<delta> Q q\<^sub>0 \<in> q\<^sub>f}"

(* This is an example for the abstraction of a DFA *)
datatype alphabet = a | b

fun lang_ab :: "alphabet \<Rightarrow> state \<Rightarrow> state" where
  "lang_ab a s = (if s = 0 then 0 else 2)" |
  "lang_ab b s = (if s = 0 \<or> s = 1 then 1 else 2)"

value "consume [a,a,a,a,a,a,a,a,b] lang_ab {0,1,2} 0 \<in> {1}"
value "consume [a,a,a,a,a,b,a,a,b] lang_ab {0,1,2} 0 \<in> {1}"

(* A DFA is correctly formed when the set of states is finite, the initial state is in the set of
   states the final states are a subset of the states and that the delta function always yields as
   a result a state that belongs to the states of the DFA *)
definition dfa :: "state set \<Rightarrow> state \<Rightarrow> state set \<Rightarrow> ('a \<Rightarrow> state \<Rightarrow> state) \<Rightarrow> bool" where
  "dfa Q q\<^sub>0 q\<^sub>f \<delta> \<equiv> finite Q \<and> q\<^sub>0 \<in> Q \<and> q\<^sub>f \<subseteq> Q \<and> (\<forall> a q. q \<in> Q \<and> \<delta> a q \<in> Q )"

(* We define injectivity for further use in the proof *)
definition injective :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "injective f A \<longleftrightarrow> (\<forall> x \<in> A. \<forall> y \<in> A . f x = f y \<longrightarrow> x = y)"

(* Auxiliary lemma to proove pidgeonhole: Assuming a set A is finite then a function f is
   is injective over the set A iff the cardinality of the image of f applied to A is equal to
   the cardinality of A *)
lemma cardi: "finite A \<Longrightarrow> injective f A \<longleftrightarrow> card {y. (\<exists>x \<in> A. y = f x)} = card A"
sorry

(* Proof of the pidgeonhole principle *)
lemma pigeonhole: "finite A \<Longrightarrow> finite B \<Longrightarrow> card B < card A \<Longrightarrow> (\<forall> x \<in> A. f x \<in> B)
  \<Longrightarrow> (\<exists> x y. x \<noteq> y \<and> f x = f y \<and> x \<in> A \<and> y \<in> A)"
proof -
  assume "(\<forall>x \<in> A. f x \<in> B)"
  from this have a: "{y. (\<exists>x \<in> A. y = f x)} \<subseteq> B" by auto
  assume "finite B"
  then have b: "card {y. (\<exists>x \<in> A. y = f x)} \<le> card B" using a and card_mono by auto
  assume "card B < card A"
  then have "card {y. (\<exists>x \<in> A. y = f x)} < card A" using b by auto
  then have c: "card {y. (\<exists>x \<in> A. y = f x)} \<noteq> card A" by auto
  assume "finite A"
  then have "\<not> injective f A" using cardi and c by auto
  thus ?thesis using injective_def by blast
qed

(* We define a function pump that is meant to "pump" a word a k number of times, that is, it yields
  the word repeated a k number of times. *)
fun pump :: "nat => 'a list \<Rightarrow> 'a list" where
  "pump 0 y = []" |
  "pump k y = pump (k - 1) y@y"

(* Finally the formalization of the pumping lemma, this lemma is usually used to proof that some 
   language is not a regular language. *)
lemma pumping: 
  assumes "dfa Q q\<^sub>0 q\<^sub>f \<delta>"
  shows "\<exists> p. p\<ge>1 \<and> (\<forall>w. w \<in> (language Q q\<^sub>0 q\<^sub>f \<delta>) \<and> length w \<ge> p
        \<longrightarrow> (\<exists> x y z. w = x@y@z \<and> length y \<ge> 1 \<and> length (x@y) \<le> p \<and> (\<forall>i. i\<ge>0 
            \<longrightarrow> (x @ (pump i y) @ z) \<in> (language Q q\<^sub>0 q\<^sub>f \<delta>))))"
sorry

end
