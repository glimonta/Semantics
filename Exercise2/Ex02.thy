theory Ex02
imports "~~/src/HOL/IMP/AExp"
  "~~/src/HOL/Library/Monad_Syntax"
begin

(* Exercise 2.1 *)

fun subst :: "vname \<Rightarrow> aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
  "subst x e (N n) = (N n)"
| "subst x e (V y) = (if x = y then e else V y)"
| "subst x e (Plus n m) = Plus (subst x e n) (subst x e m)"

value "subst ''x'' (Plus (V ''z'') (N 2)) (Plus (V ''x'') (Plus (V ''y'') (Plus (N 1) (V ''x''))))"

lemma subst_lemma: "aval (subst x a' a) s = aval a (s(x:=aval a' s))"
  apply(induction a)
  apply auto
  done

lemma "aval a1 s = aval a2 s \<Longrightarrow> aval (subst x a1 a) s = aval (subst x a2 a) s"
  apply (subst subst_lemma)
  apply (subst subst_lemma)
  apply (simp only:)
  done

(* it works with induction too, but they wanted us to use the subst_lemma we proved before *)

(* Exercise 2.3 *)

fun vars :: "aexp \<Rightarrow> vname set" where
  "vars (N _)      = {}"
| "vars (V x)      = {x}"
| "vars (Plus x y) = vars x \<union> vars y"

lemma ndep: "x \<notin> vars e \<Longrightarrow> aval e (s(x:=v)) = aval e s"
  by (induction e) auto

(* Exercise 2.2 *)

datatype aexp' = N' int | V' vname | Plus' aexp' aexp' | PI vname | Div' aexp' aexp' 

fun aval' :: "aexp' \<Rightarrow> state \<Rightarrow> (val\<times>state) option" where
  "aval' (N' n) s = Some(n,s)"
| "aval' (V' x) s = Some(s x, s)"
| "aval' (PI x) s = Some(s x, s(x:=(s x + 1)))"
| "aval' (Plus' n m) s = (
    case aval' n s of
      None \<Rightarrow> None |
      Some(v1, s') \<Rightarrow> (
        case aval m s' of 
          None \<Rightarrow> None |
          Some(v2, s'') \<Rightarrow> Some(v1+v2, s'')
        )
    )"
| "aval' (Div' x y) s = (
    case aval' x s of
      None \<Rightarrow> None |
      Some(v1, s') \<Rightarrow> (
        case aval' y s' of 
          None \<Rightarrow> None |
          Some(v2, s'') \<Rightarrow> (if v2 = 0 then None else Some(v1 div v2, s''))
        )
    )"


(* div zero return none otherwise some *)"

lemma "aval' a s = (v, s') \<Longrightarrow> s x \<le> s' x"
  apply(induction a arbitrary: s s' v) 
  apply(auto split: prod.split_asm) [2]
  (* We can use 'try' when we don't know how to proceed and auto failed us, it will look
     for a lemma or something that proves our lemma.
     Using fastforce can be unstable because what it does depends on the output of auto, and
     with a different version of Isabelle this output may change *)
  apply (fastforce split: prod.split_asm)
  apply (auto split: prod.split_asm) []
  done


                                             
end
