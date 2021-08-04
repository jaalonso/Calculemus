(* Una_funcion_tiene_inversa_si_y_solo_si_es_biyectiva.thy
-- Una función tiene inversa si y solo si es biyectiva
-- José A. Alonso Jiménez
-- Sevilla, 10 de agosto de 2021
-- ------------------------------------------------------------------ *)

(* ---------------------------------------------------------------------
-- En Isabelle se puede definir que g es una inversa de f por
--    definition inversa :: "('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool" where
--      "inversa f g \<longleftrightarrow> (\<forall> x. (g \<circ> f) x = x) \<and> (\<forall> y. (f \<circ> g) y = y)"
-- y que f tiene inversa por
--    definition tiene_inversa :: "('a \<Rightarrow> 'b) \<Rightarrow> bool" where
--      "tiene_inversa f \<longleftrightarrow> (\<exists> g. inversa f g)"
--
-- Demostrar que la función f tiene inversa si y solo si f es biyectiva.
-- ------------------------------------------------------------------ *)

theory Una_funcion_tiene_inversa_si_y_solo_si_es_biyectiva
imports Main
begin

definition inversa :: "('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool" where
  "inversa f g \<longleftrightarrow> (\<forall> x. (g \<circ> f) x = x) \<and> (\<forall> y. (f \<circ> g) y = y)"

definition tiene_inversa :: "('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "tiene_inversa f \<longleftrightarrow> (\<exists> g. inversa f g)"

(* 1\<ordfeminine> demostración *)
lemma "tiene_inversa f \<longleftrightarrow> bij f"
proof (rule iffI)
  assume "tiene_inversa f"
  then obtain g where h1 : "\<forall> x. (g \<circ> f) x = x" and
                      h2 : "\<forall> y. (f \<circ> g) y = y"
    using inversa_def tiene_inversa_def by metis
  show "bij f"
  proof (rule bijI)
    show "inj f"
    proof (rule injI)
      fix x y
      assume "f x = f y"
      then have "g (f x) = g (f y)"
        by simp
      then show "x = y"
        using h1 by simp
    qed
  next
    show "surj f"
    proof (rule surjI)
      fix y
      show "f (g y) = y"
        using h2 by simp
    qed
  qed
next
  assume "bij f"
  then have "surj f"
    by (rule bij_is_surj)
  then obtain g where hg : "\<forall>y. f (g y) = y"
    by (metis surjD)
  have "inversa f g"
  proof (unfold inversa_def; intro conjI)
    show "\<forall>x. (g \<circ> f) x = x"
    proof (rule allI)
      fix x
      have "inj f"
        using \<open>bij f\<close> by (rule bij_is_inj)
      then show "(g \<circ> f) x = x"
      proof (rule injD)
        have "f ((g \<circ> f) x) = f (g (f x))"
          by simp
        also have "\<dots> = f x"
          by (simp add: hg)
        finally show "f ((g \<circ> f) x) = f x"
          by this
      qed
    qed
  next
    show "\<forall>y. (f \<circ> g) y = y"
      by (simp add: hg)
  qed
  then show "tiene_inversa f"
    using tiene_inversa_def by auto
qed

(* 2\<ordfeminine> demostración *)
lemma "tiene_inversa f \<longleftrightarrow> bij f"
proof (rule iffI)
  assume "tiene_inversa f"
  then obtain g where h1 : "\<forall> x. (g \<circ> f) x = x" and
                      h2 : "\<forall> y. (f \<circ> g) y = y"
    using inversa_def tiene_inversa_def by metis
  show "bij f"
  proof (rule bijI)
    show "inj f"
    proof (rule injI)
      fix x y
      assume "f x = f y"
      then have "g (f x) = g (f y)"
        by simp
      then show "x = y"
        using h1 by simp
    qed
  next
    show "surj f"
    proof (rule surjI)
      fix y
      show "f (g y) = y"
        using h2 by simp
    qed
  qed
next
  assume "bij f"
  have "inversa f (inv f)"
  proof (unfold inversa_def; intro conjI)
    show "\<forall>x. (inv f \<circ> f) x = x"
      by (simp add: \<open>bij f\<close> bij_is_inj)
  next
    show "\<forall>y. (f \<circ> inv f) y = y"
      by (simp add: \<open>bij f\<close> bij_is_surj surj_f_inv_f)
  qed
  then show "tiene_inversa f"
    using tiene_inversa_def by auto
qed

end
