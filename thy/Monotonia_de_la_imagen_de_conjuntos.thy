(* Monotonia_de_la_imagen_de_conjuntos.thy
   Monotonía de la imagen de conjuntos
   José A. Alonso Jiménez
   Sevilla, 12 de junio de 2021
   ---------------------------------------------------------------------
*)

text \<open>------------------------------------------------------------------
   Demostrar que si s \<subseteq> t, entonces
      f ` s \<subseteq> f ` t
  ---------------------------------------------------------------------\<close>

theory Monotonia_de_la_imagen_de_conjuntos
imports Main
begin

section \<open>1\<ordfeminine> demostración\<close>

lemma
  assumes "s \<subseteq> t"
  shows "f ` s \<subseteq> f ` t"
proof (rule subsetI)
  fix y
  assume "y \<in> f ` s"
  then show "y \<in> f ` t" 
  proof (rule imageE)
    fix x
    assume "y = f x"
    assume "x \<in> s"
    then have "x \<in> t" 
      using \<open>s \<subseteq> t\<close> by (simp only: set_rev_mp)
    then have "f x \<in> f ` t"
      by (rule imageI)
    with \<open>y = f x\<close> show "y \<in> f ` t"  
      by (rule ssubst)
  qed
qed

section \<open>2\<ordfeminine> demostración\<close>

lemma
  assumes "s \<subseteq> t"
  shows "f ` s \<subseteq> f ` t"
proof
  fix y
  assume "y \<in> f ` s"
  then show "y \<in> f ` t" 
  proof
    fix x
    assume "y = f x"
    assume "x \<in> s"
    then have "x \<in> t" 
      using \<open>s \<subseteq> t\<close> by (simp only: set_rev_mp)
    then have "f x \<in> f ` t"
      by simp
    with \<open>y = f x\<close> show "y \<in> f ` t"  
      by simp
  qed
qed

section \<open>3\<ordfeminine> demostración\<close>

lemma
  assumes "s \<subseteq> t"
  shows "f ` s \<subseteq> f ` t"
  using assms
  by blast

section \<open>4\<ordfeminine> demostración\<close>

lemma
  assumes "s \<subseteq> t"
  shows "f ` s \<subseteq> f ` t"
  using assms
  by (simp only: image_mono)

end
