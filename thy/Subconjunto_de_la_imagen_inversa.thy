(* Subconjunto_de_la_imagen_inversa.thy
   Subconjunto de la imagen inversa
   José A. Alonso Jiménez
   Sevilla, 8 de junio de 2021
   ---------------------------------------------------------------------
*)

text \<open>------------------------------------------------------------------
   Demostrar que
      f[s] \<subseteq> u \<leftrightarrow> s \<subseteq> f⁻¹[u]
  ---------------------------------------------------------------------\<close>

theory Subconjunto_de_la_imagen_inversa
imports Main
begin

section \<open>1\<ordfeminine> demostración\<close>

lemma "f ` s \<subseteq> u \<longleftrightarrow> s \<subseteq> f -` u"
proof (rule iffI)
  assume "f ` s \<subseteq> u" 
  show "s \<subseteq> f -` u" 
  proof (rule subsetI)
    fix x
    assume "x \<in> s"
    then have "f x \<in> f ` s"
      by (simp only: imageI)
    then have "f x \<in> u" 
      using \<open>f ` s \<subseteq> u\<close> by (rule set_rev_mp) 
    then show "x \<in> f -` u" 
      by (simp only: vimageI) 
  qed
next
  assume "s \<subseteq> f -` u"
  show "f ` s \<subseteq> u" 
  proof (rule subsetI)
    fix y
    assume "y \<in> f ` s"
    then show "y \<in> u" 
    proof
      fix x
      assume "y = f x"
      assume "x \<in> s"
      then have "x \<in> f -` u" 
        using \<open>s \<subseteq> f -` u\<close> by (rule set_rev_mp)
      then have "f x \<in> u"
        by (rule vimageD)
      with \<open>y = f x\<close> show "y \<in> u" 
        by (rule ssubst)
    qed
  qed
qed

section \<open>2\<ordfeminine> demostración\<close>

lemma "f ` s \<subseteq> u \<longleftrightarrow> s \<subseteq> f -` u"
proof
  assume "f ` s \<subseteq> u" 
  show "s \<subseteq> f -` u" 
  proof
    fix x
    assume "x \<in> s"
    then have "f x \<in> f ` s"
      by simp
    then have "f x \<in> u" 
      using \<open>f ` s \<subseteq> u\<close> by (simp add: set_rev_mp) 
    then show "x \<in> f -` u" 
      by simp
  qed
next
  assume "s \<subseteq> f -` u"
  show "f ` s \<subseteq> u" 
  proof
    fix y
    assume "y \<in> f ` s"
    then show "y \<in> u" 
    proof
      fix x
      assume "y = f x"
      assume "x \<in> s"
      then have "x \<in> f -` u" 
        using \<open>s \<subseteq> f -` u\<close> by (simp only: set_rev_mp)
      then have "f x \<in> u"
        by simp
      with \<open>y = f x\<close> show "y \<in> u" 
        by simp
    qed
  qed
qed

section \<open>3\<ordfeminine> demostración\<close>

lemma "f ` s \<subseteq> u \<longleftrightarrow> s \<subseteq> f -` u"
  by (simp only: image_subset_iff_subset_vimage)

section \<open>4\<ordfeminine> demostración\<close>

lemma "f ` s \<subseteq> u \<longleftrightarrow> s \<subseteq> f -` u"
  by auto

end
