theory Ex04
imports Main
begin

(* Exercise 4.1 *)

(* Podemos definir esto de dos maneras, como un conjunto o como una relacion *)
inductive star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for step where
  "star step x x" |
  "\<lbrakk> star step x y; step y z \<rbrakk> \<Longrightarrow> star step x z"

inductive_set starp' :: "('a \<times> 'a) set \<Rightarrow> ('a \<times> 'a) set" for R where
  "(x,x) \<in> starp' R" |
  "\<lbrakk>(x,y) \<in> starp' R; (y, z) \<in> R \<rbrakk> \<Longrightarrow> (x,z) \<in> starp' R"

(* La primera definicion que hicimos le pega un paso al final, pero tambien podemos agregar pasos
   al inicio, como sigue: *)
inductive star' :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for step where
  "star' step x x" |
  "\<lbrakk>step x y; star' step y z\<rbrakk> \<Longrightarrow> star' step x z"

lemma star_prepend: (* \<lbrakk> step x y; star step y z \<rbrakk> \<Longrightarrow> star step x z *)
  assumes 1: "step x y"
  assumes 2: "star step y z"
  shows "star step x z"
    using 2 1
    apply (induction)
    apply (auto intro: star.intros) (* usamos las reglas de intro de star porque en C tenemos star *)
  done

lemma star'_append: (* \<lbrakk> star step x y; step y z \<rbrakk> \<Longrightarrow> star step x z *)
  assumes 1: "star' step x y"
  assumes 2: "step y z"
  shows "star' step x z"
    using 1 2
    apply (induction)
    apply (auto intro: star'.intros) (* usamos las reglas de la definicion inductiva de star porque en la conclusion tenemos star *)
  done

lemma "star = star'"
proof (intro ext iffI) (* agregamos iffI porque tenemos una igualdad y necesitamos probar ambas direcciones *)
  fix R :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and x y :: 'a
  assume "star R x y"
  then show "star' R x y"
    apply induction
    apply (auto intro: star'.intros star'_append)
  done
next
  fix R :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and x y :: 'a
  assume "star' R x y"
  then show "star R x y"
    apply induction
    apply (auto intro: star.intros star_prepend)
  done
qed

(* Exercise 4.2 *)
fun elems :: "'a list \<Rightarrow> 'a set" where
  "elems [] = {}"
| "elems (x#xs) = insert x (elems xs)"

value "elems [1,2,3,4::nat]"

lemma "elems [1,2,3,4::nat] = {1,2,3,4}"
sorry

lemma (* "x \<in> elems xs \<Longrightarrow> \<exists> ys zs. xs = ys @ x # zs \<and> x \<notin> elems ys" *)
  assumes "x \<in> elems xs"
  shows "\<exists> ys zs. xs = ys @ x # zs \<and> x \<notin> elems ys"
  using assms
proof (induction xs)
  case Nil hence False by simp thus ?case ..
next
  case (Cons y xs')
  (* note `x \<in> elems (y#xs')` esto ya lo sabemos, es para documentar, es como decir: ya se esto *)
  assume A: "x \<in> elems (y#xs')"
  assume IH: "x \<in> elems xs' \<Longrightarrow> \<exists> ys zs. xs' = ys @ x # zs \<and> x \<notin> elems ys"
  term ?case
  show "\<exists> ys zs. xs' = ys @ x # zs \<and> x \<notin> elems ys"
  proof (cases)
    assume "x = y"
    hence "y#xs' = [] @ x # xs' \<and> x \<notin> elems []"
      by simp
    thus ?case by blast
    show ?thesis sorry
  next
    assume "x \<noteq> y"
    show ?thesis sorry
  qed
qed


(* Exercise 4.3 *)
inductive ev :: "nat \<Rightarrow> bool" where
  ev0: "ev 0" |
  evSS: "ev n \<Longrightarrow> ev (Suc (Suc n))"

lemma "ev (Suc (Suc n)) \<Longrightarrow> ev n"
sorry

end
