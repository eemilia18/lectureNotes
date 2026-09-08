// #Sireum #Logika

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._



@pure def or1(a: B, b: B, c: B): Unit = {
    Deduce(
        (a) |- (b | a | c)
        Proof(
            //PROOF GOES HERE
            1 ( a )     by Premise
        )
    )
}