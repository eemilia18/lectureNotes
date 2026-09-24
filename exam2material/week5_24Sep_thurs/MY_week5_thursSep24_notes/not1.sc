// #Sireum #Logika

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

@pure def not1(p: B, q: B, r: B): Unit = {
  Deduce(
    ( p __>: !q ) |- ( !(p & q)  )
      Proof(
      1 (  p __>: !q ) by Premise,
      
      2 SubProof(
        3 Assume (p & q),
        4 ( p ) by AndE1(3),
        5 ( q ) by AndE2(3), 
        6 ( !q ) by ImplyE(1, 4),
        7 ( F ) by NegE(5, 6), 
        //goal: F
      ),
      8 (!(p & q)) by NegI(2),
      //goal: introduce a NOT to get !(p & q) 
    )
  )
}