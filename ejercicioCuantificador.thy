theory ejercicioCuantificador
imports Main
begin

lemma lp1:
  assumes 1: "\<forall>x. (D(x)\<longrightarrow> T(x))" and
          2: "\<forall>x. (D(x) \<and> T(x)) \<longrightarrow> R(x)" and
          3: "D(a)"
        shows "R(a)"
proof -
  have 4: "D(a) \<longrightarrow> T(a)" using 1 by (rule allE)
  have 5: "(D(a) \<and> T(a)) \<longrightarrow> R(a)" using 2 by (rule allE)
  have 6: "T(a)" using 4 3 by (rule mp)
  have 7: "D(a) \<and> T(a)" using 3 6 by (rule conjI)
  show "R(a)" using 5 7 by (rule mp)
qed

thm allI

lemma lb22:
  assumes 1: "\<forall>x. (P(x) \<and> Q(x))" and
          2: "\<forall>x. P (x)"
        shows "\<forall>x. Q(x)"
proof - 
  {
    fix a
    have 3: "P(a) \<and> Q(a)" using 1 by (rule allE)
    have 4: "Q(a)" using 3 by (rule conjunct2)
  }
  then show "\<forall>x. Q(x)" by (rule allI)
qed

thm exI

lemma lp4:
  assumes 1: "\<forall>x. P(x)"
  shows "\<exists>x. P(x)"
proof -
  fix a
  have 2: "P(a)" using 1 by (rule allE)
  show "\<exists>x. P(x)" using 2 by (rule exI)
qed

(*Cuantificador existencial*)

lemma lp3:
  assumes 1: "\<forall>x. (P(x) \<longrightarrow> Q(x))" and
          2: "\<exists>x. P(x)"
        shows "\<exists>x. Q(x) \<or> R(x)"
proof - 
  obtain a where 3: "P(a)" using 2 by (rule exE)
  have 4: "P(a) \<longrightarrow> Q(a)" using 1 by (rule allE)
  have 5: "Q(a)" using 4 3 by (rule mp)
  have 6: "Q(a) \<or> R(a)" using 5 by (rule disjI1)
  show "\<exists>x. Q(x) \<or> R(x)" using 6 by (rule exI)
qed

lemma mt: "\<lbrakk>F \<longrightarrow> \<not>G; G \<rbrakk> \<Longrightarrow> \<not>F"
  by auto