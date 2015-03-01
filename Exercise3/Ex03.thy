theory Ex03
imports Main "~~/src/HOL/IMP/AExp"
begin

inductive odd :: "nat \<Rightarrow> bool" where
odd1: "odd 1"
  | odd_add: "odd n \<Longrightarrow> odd (n+2)"

thm odd1 odd_add

(* Exercise 3.1 *)
inductive is_aval :: "aexp \<Rightarrow> state \<Rightarrow> val \<Rightarrow> bool" where
  N: "is_aval (N n) s n"
| V: "is_aval (V x) s (s x)"
| P: "\<lbrakk> is_aval a1 s v1; is_aval a2 s v2 \<rbrakk> \<Longrightarrow> is_aval (Plus a1 a2) s (v1 + v2)"

(* Step by step proof 
   We can also use apply(rule N V P)+
   or apply(rule is_val.intros)+
   or apply(intro is_aval.intros)
*)
lemma "is_aval (Plus (N 2) (Plus (V x) (N 3))) s (2+(s x + 3))"
  apply(rule P)
  apply(rule N)
  apply(rule P)
  apply(rule V)
  apply(rule N)
  done

theorem "is_aval a s v \<longleftrightarrow> aval a s = v"
proof (* this is the default rule(rule iffI) *)
  assume "is_aval a s v"
  (* then show "aval a s = v" by induction auto *)
  (* thus "aval a s = v" by induction auto *)
  thus "aval a s = v"
  proof induction
    print_cases
    case (N n s) show ?case by simp
      thm aval.simps
  next
    case (V x s) show ?case by simp
  next
    case (P a1 s v1 a2 v2)
      (* thm P.IH IH *)
      (* thm P.hyps additional hyps *)
      (* thm P.prems additional premises, we dont have those here *)
    have "aval (Plus a1 a2) s = aval a1 s + aval a2 s" by simp
    also from P.IH have "... = v1 + v2" by simp (* "..." are bound to the RHS of the last equation *)
    finally show ?case . (* "." means by assumption *)
  qed
next
  assume "aval a s = v" thus "is_aval a s v"
  proof induction
    case (N v) thus ?case by (simp add: is_aval.N)
  next
    case (V x) thus ?case
      by (auto simp add: is_aval.V)
  next
    case (Plus a1 a2)
    from Plus.prems have foo: "v = aval a1 s + aval a2 s" by simp
    thm Plus.IH
    show ?case
      unfolding foo
      apply(rule is_aval.P)
      thm Plus.IH
      apply(rule Plus.IH, simp)
      apply(rule Plus.IH, simp)
      done
      oops

(*  by (induction a arbitrary: v) (auto intro: N V P) *)
    
end
