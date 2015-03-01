theory tut05
imports "~~/src/HOL/IMP/Big_Step"
begin

  abbreviation "Or b1 b2 \<equiv> Not (And (Not b1) (Not b2))"

  lemma "IF (And b1 b2) THEN c1 ELSE c2 
      \<sim> IF b1 THEN IF b2 THEN c1 ELSE c2 ELSE c2"
    by (fastforce split: split_if_asm intro: IfTrue IfFalse)
    

  lemma "IF (And b1 b2) THEN c1 ELSE c2 
      \<sim> IF b1 THEN IF b2 THEN c1 ELSE c2 ELSE c2"
    apply (auto split: split_if_asm)
    apply (rule IfTrue)
    apply assumption
    apply (rule IfTrue)
    apply assumption
    apply assumption
    
    apply (rule IfTrue)
    apply assumption
    apply (rule IfFalse)
    apply assumption
    apply assumption

    apply (rule IfFalse)
    apply assumption
    apply assumption
    done

  lemma aux:
    assumes "(WHILE (Bc True) DO c ,s) \<Rightarrow> s'" 
    shows False
    using assms
    apply (induction "WHILE (Bc True) DO c" s s' rule: big_step_induct)
    apply auto
    done    


  lemma 
    defines "b1 \<equiv> Bc True" and "b2 \<equiv> Bc False" and "c\<equiv>SKIP"
    shows "\<not>(WHILE (And b1 b2) DO c \<sim> WHILE b1 DO WHILE b2 DO c)"
    unfolding b1_def b2_def
    apply auto
    apply (rule exI[where x="<>"])
    apply (rule exI[where x="<>"])
    apply (auto dest: aux)
    done

  lemma 
    defines "b1 \<equiv> Bc True" and "b2 \<equiv> Bc False" and "c\<equiv>SKIP"
    shows "\<not>(WHILE (And b1 b2) DO c 
      \<sim> WHILE b1 DO c;; WHILE (And b1 b2) DO c)"
    unfolding b1_def b2_def
    apply auto
    apply (rule exI[where x="<>"])
    apply (rule exI[where x="<>"])
    apply auto
    apply (auto dest: aux)
    done

  lemma aux2: 
    assumes "(WHILE b DO c,s) \<Rightarrow> t"  
    shows "\<not>bval b t"
    using assms
    apply (induction "WHILE b DO c" s t rule: big_step_induct)
    apply auto
    done

  lemma
    shows "WHILE (Or b1 b2) DO c 
      \<sim> WHILE (Or b1 b2) DO c;; WHILE b1 DO c"
    apply (auto)
    apply (frule aux2) (* drule: delete assumption, frule: Keep assumption *)

    (* This: *)
    apply (rule Seq)
    apply assumption
    apply (rule WhileFalse)
    apply (simp split: split_if_asm)

    (* Or just: *)
    (*apply (auto split: split_if_asm) []*)

    apply (frule aux2)
    (* by auto, or isar-proof:*)
  proof -
    fix s t s\<^sub>2 
    assume 1: "(WHILE Or b1 b2 DO c, s) \<Rightarrow> s\<^sub>2" 
    assume 2: "(WHILE b1 DO c, s\<^sub>2) \<Rightarrow> t"
    assume 3: "\<not> bval (Or b1 b2) s\<^sub>2"

    from 2 3 have "s\<^sub>2 = t"
      apply cases
      apply auto
      done

    with 1 show "(WHILE Or b1 b2 DO c, s) \<Rightarrow> t" by simp
  qed
    


  term "op \<sim>"




end

