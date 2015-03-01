theory Ex01
imports Main
begin

(* Exercise 1.1 *)
                                  
value "2 + (2::nat)"
value "(2::nat) * (5 + 3)"
value "(3::nat) * 4 - 2 * (7 + 1)"

(* Exercise 1.2 *)

lemma nat_add_comm: "(a::nat) + b = b + a"
  by auto

lemma nat_add_assoc: 
  fixes a b c :: nat 
  shows "(a + b) + c = a + (b + c)"
  by auto

lemma 
  fixes a b c :: nat 
  shows "(a + b) + c = a + (c + b)"
  by auto

(* Exercise 1.3 *)

fun count :: "'a list \<Rightarrow> 'a \<Rightarrow> nat" where
  "count []     e = 0"
| "count (x#xs) e = (if x = e then 1 + count xs e else count xs e)"

value "count [] 1"
value "count [1::nat,2,4,5,2,3,1,3,4,1] 1"

theorem "count xs x \<le> length xs"
  apply(induction xs)
  apply(auto)
  done

(* Exercise 1.4 *)

fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "snoc []     e = e # []"
| "snoc (x#xs) e = x # snoc xs e"

value "snoc [] 2"
value "snoc [1,2,3] (4::int)"

lemma "snoc [] e = [e]"
  by auto

fun reverse :: "'a list \<Rightarrow> 'a list" where
  "reverse []     = []"
| "reverse (x#xs) = snoc (reverse xs) x"

value "reverse []"
value "reverse [1,2,4,5,3::int]"
value "reverse [a,b,c]"

lemma "reverse [a,b,c] = [c,b,a]"
  by auto

lemma aux: "reverse (snoc xs x) = (x # (reverse xs))"
  apply(induction xs)
  apply(auto)
  done

theorem "reverse (reverse xs) = xs"
  apply(induction xs)
  apply(auto simp: aux)
  done

(* Homework 1.1 *)

fun pow2 :: "nat \<Rightarrow> nat" where
  "pow2 0       = 1"
| "pow2 (Suc n) = 2 * pow2 n"

value "pow2 3 = 8"

(* 
   Informal proof of "pow2 (n + m) = pow2 n * pow2 m"

   We use induction over n.
   Base case n=0:
   pow2 (0 + m) = pow2 0 * pow2 m
 =  < 0 + m = m >
   pow2 m = pow2 0 * pow2 m
 =  < pow2 0 = 1 >
   pow2 m = 1 * pow2 m
 =  < 1 * m = m, in which [m:=pow2 m] >
   pow2 m = pow2 m

   Inductive case: 
   (IH): pow2 (n + m) = pow2 n * pow2 m

   pow2 ((Suc n) + m) = pow2 (Suc n) * pow2 m
 =  < pow2 (Suc n) = 2 * pow2 n >
   pow2 ((Suc n) + m) = (2 * pow2 n) * pow2 m >
 =  < (a*b)*c = a*(b*c), in which [a,b,c:=2,pow2 n, pow2 m] >
   pow2 ((Suc n) + m) = 2 * (pow2 n * pow2 m)
 =  < Using Inductive Hypothesis >
   pow2 ((Suc n) + m) = 2 * pow2 (n + m)
 =  < (Suc n) + m = Suc(n + m) >
   pow2 (Suc(n + m)) = 2 * pow2 (n + m)
 =  < pow2 (Suc n() = 2 * pow2 n, in which [n:=n+m] >
   2 * pow2 (n + m) = 2 * pow2 (n + m)

*)

lemma "pow2 (n + m) = pow2 n * pow2 m"
  apply(induction n)
  apply(auto)
  done

(* Homework 1.2 *)

fun double :: "'a list \<Rightarrow> 'a list" where
  "double []       = []"
| "double (x # xs) = x # x # double xs"

value "double []"
value "double [a,b,c,d]"

lemma aux2: "double(xs @ [x]) = double xs @ [x,x]"
  apply(induction xs)
  apply(auto)
  done

lemma rev_double: "rev(double xs) = double(rev xs)"
  apply(induction xs)
  apply(auto simp: aux2)
  done

end
