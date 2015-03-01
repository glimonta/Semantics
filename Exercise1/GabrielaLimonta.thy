theory GabrielaLimonta
imports Main
begin

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
 =  < Using Inductive Hypothesis (IH) >
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

lemma aux: "double(xs @ [x]) = double xs @ [x,x]"
  apply(induction xs)
  apply(auto)
  done

lemma rev_double: "rev(double xs) = double(rev xs)"
  apply(induction xs)
  apply(auto simp: aux)
  done

end
