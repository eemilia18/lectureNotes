// #Sireum #Logika

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._


//Complete the following natural deduction proof.
//When you are finished, your file should say "Logika verified".

//p, q ∧ s, ¬r ⊢ (r ∨ s) ∧ (¬p ∨ q ∧ ¬r)


@pure def deduction5(p: B, q: B, r: B, s: B): Unit = {
  Deduce(
    //@formatter: off

    (p, q & s, !r) |- ((r | s) & (!p | q & !r))
      Proof(
      1 (  p                        ) by Premise,
      2 (  q & s                    ) by Premise,
      3 (  !r                       ) by Premise,
      4 (  q                        ) by AndE1(2),
      5 (  s                        ) by AndE2(2),
      6 (  q & !r                   ) by AndI(4, 3),
      7 (  !p | q & !r              ) by OrI2(6),
      8 (  r | s                    ) by OrI2(5),
      9 (  (r | s) & (!p | q & !r)  ) by AndI(8, 7)
    )
    //@formatter:on
  )
}