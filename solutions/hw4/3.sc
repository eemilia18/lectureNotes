// #Sireum #Logika

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._


//Complete the following natural deduction proof.
//When you are finished, do a Logika check.
//Your file should say "Logika verified".

//p ∧ q → r ⊢ p → (q → r)

@pure def hw4_prob3(p: B, q: B, r: B): Unit = {
  Deduce(
    (p & q __>: r) |-  ( p __>: (q __>: r) )
      Proof(
      1 (  p & q __>: r        ) by Premise,
      2 SubProof(
        3 Assume(  p  ),
        4 SubProof(
          5 Assume (  q  ),
          6 (  p & q        ) by AndI(3, 5),
          7 (  r            ) by ImplyE(1, 6)
          //goal: r
        ),
        8 (  q __>: r          ) by ImplyI(4)
        //goal: q __>: r
      ),
      9 (  p __>: (q __>: r)      ) by ImplyI(2)
    )
  )
}
