(* Union_con_su_diferencia.thy
   Unión con su diferencia
   José A. Alonso Jiménez
   Sevilla, 27 de mayo de 2021
   ---------------------------------------------------------------------
*)

text \<open>------------------------------------------------------------------
  Demostrar que
     (s \ t) \<union> t = s \<union> t
  ---------------------------------------------------------------------\<close>

theory Union_con_su_diferencia
imports Main
begin

section \<open>1\<ordfeminine> demostración: Detallada\<close>

lemma "(s - t) \<union> t = s \<union> t"
proof (rule equalityI)
  show "(s - t) \<union> t \<subseteq> s \<union> t" 
  proof (rule subsetI)
    fix x
    assume "x \<in> (s - t) \<union> t" 
    then show "x \<in> s \<union> t" 
    proof (rule UnE)
      assume "x \<in> s - t"
      then have "x \<in> s"
        by (simp only: DiffD1)
      then show "x \<in> s \<union> t" 
        by (simp only: UnI1)
    next
      assume "x \<in> t"  
      then show "x \<in> s \<union> t" 
        by (simp only: UnI2)
    qed
  qed
next
  show "s \<union> t \<subseteq> (s - t) \<union> t" 
  proof (rule subsetI)
    fix x
    assume "x \<in> s \<union> t" 
    then show "x \<in> (s - t) \<union> t" 
    proof (rule UnE)
      assume "x \<in> s"
      show "x \<in> (s - t) \<union> t" 
      proof (cases \<open>x \<in> t\<close>)
        assume "x \<in> t" 
        then show "x \<in> (s - t) \<union> t" 
          by (simp only: UnI2)
      next
        assume "x \<notin> t" 
        with \<open>x \<in> s\<close> have "x \<in> s - t"
          by (rule DiffI)
        then show "x \<in> (s - t) \<union> t" 
          by (simp only: UnI1)
      qed
    next
      assume "x \<in> t" 
      then show "x \<in> (s - t) \<union> t"
        by (simp only: UnI2)
    qed
  qed
qed

section \<open>2\<ordfeminine> demostración: Estructurada\<close>

lemma "(s - t) \<union> t = s \<union> t"
proof
  show "(s - t) \<union> t \<subseteq> s \<union> t" 
  proof
    fix x
    assume "x \<in> (s - t) \<union> t" 
    then show "x \<in> s \<union> t" 
    proof 
      assume "x \<in> s - t"
      then have "x \<in> s"
        by simp
      then show "x \<in> s \<union> t" 
        by simp
    next
      assume "x \<in> t"  
      then show "x \<in> s \<union> t" 
        by simp
    qed
  qed
next
  show "s \<union> t \<subseteq> (s - t) \<union> t" 
  proof
    fix x
    assume "x \<in> s \<union> t" 
    then show "x \<in> (s - t) \<union> t" 
    proof
      assume "x \<in> s"
      show "x \<in> (s - t) \<union> t" 
      proof 
        assume "x \<notin> t" 
        with \<open>x \<in> s\<close> show "x \<in> s - t"
          by simp
      qed
    next
      assume "x \<in> t" 
      then show "x \<in> (s - t) \<union> t" 
        by simp
    qed
  qed 
qed

section \<open>3\<ordfeminine> demostración: Con lema\<close>

lemma "(s - t) \<union> t = s \<union> t"
by (fact Un_Diff_cancel2) 

section \<open>4\<ordfeminine> demostración: Automática\<close>

lemma "(s - t) \<union> t = s \<union> t"
  by auto

end
