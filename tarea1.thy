theory tarea1
    imports Main
begin

lemma ejemplo:
    assumes 1: "(t \<or> u) \<or> w" 
    shows "t \<or> (u \<or> w)" 
      using 1
    proof(rule disjE)
      {
        assume 2: "t \<or> u"
        show "t \<or> (u \<or> w)" 
          using 2
     proof  (rule disjE)
       {
         assume 3: "t"
         show "t \<or> (u \<or> w)" using 3 by (rule disjI1)
       }
     next 
       {
          assume 4: "u"
          have 5: "u \<or> w" using 4 by (rule disjI1)
          show "t \<or> (u \<or> w)" using 5 by (rule disjI2)
        }
    qed
    next
      {
        assume 6: "w"
        have 7: "u \<or> w" using 6 by (rule disjI2)
        show "t \<or> (u \<or> w)" using 7 by (rule disjI2)
      }
    }
  qed