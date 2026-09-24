// #Sireum #Logika

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

@pure def not2(p: B, q: B, r: B): Unit = {
  Deduce(
    ( !p & !q ) |- ( !(p | q)  )
      Proof(
        1 (  !p & !q ) by Premise,
        2 ( !p ) by AndE1(1),
        3 ( !q ) by AndE2(1),
        4 SubProof(
          5 Assume (p | q), 
          6 SubProof(
            7 Assume (p),
            8( F ) by NegE(7, 2), 
          ),
          9 SubProof(
            10 Assume ( q ), 
            11 ( F ) by NegE(10, 3),
          ), 
          12 ( F ) by OrE(5, 6, 9), 
        ),
        13 (!(p | q)) by NegI(4), 

    )
  )
}