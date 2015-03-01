theory GabrielaLimonta
imports "~~/src/HOL/IMP/AExp"
begin
(** Score: 15/10 *)
(* Homework 2.1 *)
datatype bst = Leaf | node int bst bst

fun \<alpha> :: "bst \<Rightarrow> (int) set" where
  "\<alpha> Leaf = {}"
| "\<alpha> (node e l r) = {e} \<union> \<alpha> l \<union> \<alpha> r"

value "\<alpha> (node 4 (node 2 (node 1 Leaf Leaf) (node 3 Leaf Leaf)) (node 5 Leaf Leaf))"

fun invar :: "bst \<Rightarrow> bool" where
  "invar Leaf = True"
| "invar (node e l r) = (invar l \<and> invar r \<and> (\<forall>x\<in>(\<alpha> l). e > x) \<and> (\<forall>x\<in>(\<alpha> r). e < x)) "

value "invar (node 4 (node 2 (node 1 Leaf Leaf) (node 3 Leaf Leaf)) (node 5 Leaf Leaf))"
value "invar (node 4 (node 1 (node 2 Leaf Leaf) (node 3 Leaf Leaf)) (node 5 Leaf Leaf))"

fun lookup :: "int \<Rightarrow> bst \<Rightarrow> bool" where
  "lookup e Leaf = False"
| "lookup e (node x l r) = (if e = x then True else (if e > x then lookup e r else lookup e l))"

value "lookup 1 Leaf"
value "lookup 1 (node 1 Leaf Leaf)"
value "lookup 1 (node 2 Leaf Leaf)"
value "lookup 1 (node 4 (node 2 (node 1 Leaf Leaf) (node 3 Leaf Leaf)) (node 5 Leaf Leaf))"
value "lookup 42 (node 4 (node 2 (node 1 Leaf Leaf) (node 3 Leaf Leaf)) (node 5 Leaf Leaf))"
value "lookup 2 (node 4 (node 1 (node 2 Leaf Leaf) (node 3 Leaf Leaf)) (node 5 Leaf Leaf))"

lemma "invar t \<Longrightarrow> lookup x t \<longleftrightarrow> x\<in>\<alpha> t"
  apply(induction t)
  apply(auto)
  done

fun ins :: "int \<Rightarrow> bst \<Rightarrow> bst" where
  "ins e Leaf = (node e Leaf Leaf)"
| "ins e (node x l r) = (if e = x then node x l r else (if e < x then node x (ins e l) r else node x l (ins e r)))"

value "ins -4(ins -9(ins 5(ins 6(ins 56(ins 9(ins 3(ins 1 Leaf)))))))"

lemma ins_correct1: "\<lbrakk>invar t\<rbrakk> \<Longrightarrow> \<alpha> (ins x t) = insert x (\<alpha> t)"
  apply(induction t)
  apply(auto)
  done

lemma ins_correct2: "invar t \<Longrightarrow> invar (ins x t)"
  apply(induction t)
  apply(auto simp add: ins_correct1)
  done

fun dell :: "int \<Rightarrow> bst \<Rightarrow> bst" where
  "dell _ Leaf = Leaf"
| "dell e (node x l r) = (if e = x then (node x Leaf r) else (if e < x then (node x (dell e l) r) else (dell e r)))"

value "dell 5 (node 4 (node 2 (node 1 Leaf Leaf) (node 3 Leaf Leaf)) (node 10 Leaf Leaf))"

lemma dell_correct1: "invar t \<Longrightarrow> \<alpha> (dell a t) = {x\<in>\<alpha> t. x\<ge>a}"
  apply(induction t)
  apply(auto)
  done

lemma dell_correct2: "invar t \<Longrightarrow> invar (dell a t)"
  apply(induction t)
  apply(auto simp add: dell_correct1)
  done

(* Homework 2.2 *)

type_synonym vname = string
type_synonym state = "string \<Rightarrow> int"
type_synonym val = "int"

declare algebra_simps[simp]

datatype aexp = N int | V vname | Plus aexp aexp | Mult int aexp

fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
"aval (N n) s = n" |
"aval (V x) s = s x" |
"aval (Plus a1 a2) s = aval a1 s + aval a2 s" |
"aval (Mult i a) s = i * aval a s"

fun normal :: "aexp \<Rightarrow> bool" where
  "normal (N n) = True"
| "normal (V x) = True"
| "normal (Mult i a) = (
    case a of
      (N n) \<Rightarrow> False |
      (V x) \<Rightarrow> True |
      (Mult i a) \<Rightarrow> False |
      (Plus a1 a2) \<Rightarrow> False)"
| "normal (Plus a1 a2) = (normal a1 \<and> normal a2)"

value "normal (Plus (N 6) (Mult 4 (V x)))"
value "normal (Plus (N 6) (Mult 4 (Mult 3 (V y))))"

fun normalize :: "aexp \<Rightarrow> aexp" where
  "normalize (N n) = (N n)"
| "normalize (V x) = (V x)"
| "normalize (Plus a1 a2) = (Plus (normalize a1) (normalize a2))"
| "normalize (Mult i a) = (
    case a of
      (N n) \<Rightarrow> (N (i*n)) |
      (V x) \<Rightarrow> (Mult i (V x)) |
      (Mult x y) \<Rightarrow> normalize (Mult (i*x) y) |
      (Plus x y) \<Rightarrow> (Plus (normalize (Mult i x)) (normalize (Mult i y)))
)"

value "normalize (Plus (N 6) (Mult 4 (Mult 3 (V y))))"
value "normalize (Mult 2 (Plus (V x) (N 21)))"

lemma aux: "aval (normalize a) s = aval a s"
  apply(induction a rule: normalize.induct)
  apply(auto split: aexp.split)
  done

lemma "normal (normalize a)"
  apply(induction a rule: normalize.induct)
  apply(auto simp add: aux split: aexp.split)
  done

end

