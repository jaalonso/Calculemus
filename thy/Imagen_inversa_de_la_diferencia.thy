(* Imagen_inversa_de_la_diferencia.thy
-- Imagen inversa de la diferencia
-- José A. Alonso Jiménez
-- Sevilla, 18 de junio de 2021
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- Demostrar que
--    f -` u - f -` v \<subseteq> f -` (u - v)
-- ------------------------------------------------------------------- *)

theory Imagen_inversa_de_la_diferencia
imports Main
begin

(* 1\<ordfeminine> demostración *)

lemma "f -` u - f -` v \<subseteq> f -` (u - v)"
proof (rule subsetI)
  fix x
  assume "x \<in> f -` u - f -` v"
  then have "f x \<in> u - v"
  proof (rule DiffE)
    assume "x \<in> f -` u"
    assume "x \<notin> f -` v"
    have "f x \<in> u" 
      using \<open>x \<in> f -` u\<close> by (rule vimageD)
    moreover
    have "f x \<notin> v" 
    proof (rule notI)
      assume "f x \<in> v"
      then have "x \<in> f -` v" 
        by (rule vimageI2)
      with \<open>x \<notin> f -` v\<close> show False 
        by (rule notE)
    qed
    ultimately show "f x \<in> u - v" 
      by (rule DiffI)
  qed
  then show "x \<in> f -` (u - v)" 
    by (rule vimageI2)
qed

(* 2\<ordfeminine> demostración *)

lemma "f -` u - f -` v \<subseteq> f -` (u - v)"
proof
  fix x
  assume "x \<in> f -` u - f -` v"
  then have "f x \<in> u - v"
  proof
    assume "x \<in> f -` u"
    assume "x \<notin> f -` v"
    have "f x \<in> u" using \<open>x \<in> f -` u\<close> by simp
    moreover
    have "f x \<notin> v" 
    proof 
      assume "f x \<in> v"
      then have "x \<in> f -` v" by simp
      with \<open>x \<notin> f -` v\<close> show False by simp
    qed
    ultimately show "f x \<in> u - v" by simp
  qed
  then show "x \<in> f -` (u - v)" by simp
qed

(* 3\<ordfeminine> demostración *)

lemma "f -` u - f -` v \<subseteq> f -` (u - v)"
  by (simp only: vimage_Diff)

(* 4\<ordfeminine> demostración *)

lemma "f -` u - f -` v \<subseteq> f -` (u - v)"
  by auto

end
