// #Sireum #Logika

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._



@pure def orComm(p: B, q: B): Unit = {
    Deduce(
        (p | q) |- (q | p)
        Proof(
            //PROOF GOES HERE
            1 ( p | q )     by Premise,
            2 SubProof(
                3 Assume ( p ), 
                4 ( q | p ) by OrI2(3), 
            ),
            5 SubProof(
                6 Assume ( q ),
                7 ( q | p ) by OrI1(6),
            ),
            //claim my common conclusion 
            //OrE line numbers:
                //og or and the assumptions
                //has to match premise 
            8 ( q | p ) by OrE(1, 2, 5)

        )
    )
}