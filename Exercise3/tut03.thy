theory tut03
imports Main "~~/src/HOL/IMP/ASM" "~~/src/HOL/IMP/AExp"
begin

inductive odd :: "nat \<Rightarrow> bool" where
odd1:  "odd 1"
 | odd_add: "odd n \<Longrightarrow> odd (n+2)"

thm odd1 odd_add


inductive is_aval :: "aexp \<Rightarrow> state \<Rightarrow> val \<Rightarrow> bool" where
  N: "is_aval (N n) s n"
| V: "is_aval (V x) s (s x)"
| P: "\<lbrakk> is_aval a1 s v1; is_aval a2 s v2 \<rbrakk> 
  \<Longrightarrow> is_aval (Plus a1 a2) s (v1+v2)"

lemma "is_aval (Plus (N 2) (Plus (V x) (N 3))) s (2+(s x + 3))"
  apply (rule N V P)
  apply (rule N V P)
  apply (rule N V P)
  apply (rule N V P)
  apply (rule N V P)
  (* or apply (intro is_aval.intros) *)
  (* or apply (rule is_aval.intros)+ *)
  (* or apply (rule N V P)+ *)
  done

notepad begin
  fix a b c d e f g h :: int
  assume "a=b"
  also assume "b < c+d+e+f+g+h"
  also assume "... \<le> d"
  also assume "d = e"
  finally have "a < e" .
end


lemma "is_aval a s v \<longleftrightarrow> aval a s = v"
proof 
  assume "is_aval a s v"
  (*thus "aval a s = v" by induction auto*)
  
  thus "aval a s = v" 
  proof induction
    print_cases
    case (N n s) show ?case by simp
      thm aval.simps
  next
    case (V x s) show ?case by simp
  next
    case (P a1 s v1 a2 v2)
    have "aval (Plus a1 a2) s = aval a1 s + aval a2 s" by simp
    also from P.IH have "\<dots> = v1 + v2" by simp
    finally show ?case .
  qed
next
  assume "aval a s = v" thus "is_aval a s v"
  proof (induction a arbitrary: v)
    case (N v) thus ?case by (simp add: is_aval.N)
  next
    case (V x) thus ?case 
      by (auto simp add: is_aval.V)
  next
    case (Plus a1 a2)
    from Plus.prems have 1: "v = aval a1 s + aval a2 s" 
      by simp
    
      thm Plus.IH
    show ?case
      unfolding 1
      apply (rule is_aval.P)
      thm Plus.IH
      apply (rule Plus.IH, simp)
      apply (rule Plus.IH, simp)
      done
  qed
    (*by (induction a arbitrary: v) (auto intro: N V P)*)
qed    




fun exec1 :: "instr \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack option" where
"exec1 (LOADI n) _ stk  =  Some (n # stk)" |
"exec1 (LOAD x) s stk  =  Some (s(x) # stk)" |
"exec1  ADD _ (a#b#stk)  =  Some ((a+b)#stk)" |
"exec1  ADD _ _  =  None"

text_raw{*}%endsnip*}

text_raw{*\snip{ASMexecdef}{1}{2}{% *}
fun exec :: "instr list \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack option" where
"exec [] _ stk = Some stk" |
"exec (i#is) s stk = (
  case exec1 i s stk of
    Some stk \<Rightarrow> exec is s stk
  | None \<Rightarrow> None)"

lemma exec_append:
  "exec (is1@is2) s stk = (
    case exec is1 s stk of
      Some stk \<Rightarrow> exec is2 s stk
    | None \<Rightarrow> None)"
apply(induction is1 arbitrary: stk)
apply (auto split: option.split)
done


lemma "exec (comp a) s stk = Some (aval a s # stk)"
  apply (induction a arbitrary: stk)
  apply (auto simp add: exec_append)
  done

end

