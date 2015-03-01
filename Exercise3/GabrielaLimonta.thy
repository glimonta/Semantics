theory GabrielaLimonta
imports Main
begin

(* Homework 3.1 *)
datatype instr = LDI int | LD nat | ST nat | ADD nat

type_synonym state = "nat \<Rightarrow> int"

fun exec :: "instr \<Rightarrow> state \<Rightarrow> state" where
  "exec (LDI i) s = s(0 := i)"
| "exec (LD n) s = s(0 := (s (n + 1)))"
| "exec (ST n) s = s((n+1) := (s 0))"
| "exec (ADD n) s = s(0 := (s 0) + (s (n + 1)))"

fun execs :: "instr list \<Rightarrow> state \<Rightarrow> state" where
  "execs [] s = s"
| "execs (x#xs) s = execs xs (exec x s)"

lemma [simp]: "\<And>s. execs (xs @ ys) s = execs ys ( execs xs s)"
  apply(induction xs)
  apply(auto)
  done

datatype expr = C int | V nat | A expr expr

fun val :: "expr \<Rightarrow> (nat \<Rightarrow> int) \<Rightarrow> int" where
  "val (C i) s = i"
| "val (V n) s = s n"
| "val (A a1 a2) s = val a1 s + val a2 s"

fun cmp :: "expr \<Rightarrow> nat \<Rightarrow> instr list" where
  "cmp (C i) n = (LDI i # ST n # [])"
| "cmp (V x) n = (LD x # ST n # [])"
| "cmp (A a1 a2) n = cmp a1 (n + 1) @ cmp a2 (n + 2) @ (LD (n+1) # ADD (n+2) # ST n # [])"

value "cmp (A (C 21) (A (V 1) (C 21))) 2"

fun maxvar :: "expr \<Rightarrow> nat" where
  "maxvar (C i) = 0"
| "maxvar (V n) = n"
| "maxvar (A a1 a2) = (if maxvar a1 > maxvar a2 then maxvar a1 else maxvar a2)"

value "maxvar (A (C 21) (A (V 1) (V 42)))"

lemma [simp]: "\<forall> n \<le> maxvar e. s n = s' n \<Longrightarrow> val e s = val e s'"
  apply(induction)
  apply(auto)
  done

lemma [simp]: "\<forall> n \<le> maxvar e. n > 0 \<Longrightarrow> s n = (execs (cmp e (n+1)) s) n"
  apply(induction)
  apply(auto)
  done

theorem "execs (cmp e (maxvar e + 1)) s 0 = val e (comp s Suc)"
proof(induction e)
  print_cases
  case C thus ?case by simp
next
  case V thus ?case by simp
next
  case A thus ?case 
oops

(* Exercise 3.2 *)
datatype ab = a | b

inductive_set S :: "ab list set" where
  A: "w \<in> S \<Longrightarrow> [a] @ w \<in> S"
| B: "w \<in> S \<Longrightarrow> w @ [b] \<in> S"
| E: "[] \<in> S"

fun only_b :: "ab list \<Rightarrow> bool" where
  "only_b [] = True"
| "only_b (x#xs) = (if x = b then only_b xs else False)"

value "only_b [b,b,b,b,b,b,b,b,b,b,b,b]"
value "only_b []"
value "only_b [b,b,b,b,b,a,b,b,b,b,b]"

fun is_ab :: "ab list \<Rightarrow> bool" where
  "is_ab [] = True" 
| "is_ab (x#xs) = (case x of
   a \<Rightarrow> (is_ab xs \<or> only_b xs) |
   b \<Rightarrow> only_b xs)" 

value "is_ab [b,b,b,b,b,b,b,b,b,b,b,b]"
value "is_ab []"
value "is_ab [b,b,b,b,b,a,b,b,b,b,b]"
value "is_ab [a,a,a,a,a,a,b,b,b]"
value "is_ab [a,a,a,a,a,a]"
value "is_ab [b,a]"

lemma [simp]: "(a#w) = [a] @ w"
  apply(auto)
  done

lemma "w \<in> S \<Longrightarrow> is_ab w"
proof (induction w)
  print_cases
  case Nil thus ?case by simp
next
  case (Cons e w)
  thus ?case by (auto split: ab.split)
qed

end
