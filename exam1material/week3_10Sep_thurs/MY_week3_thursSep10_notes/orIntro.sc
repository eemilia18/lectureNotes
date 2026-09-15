// #Sireum #Logika

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._



@pure def orIntro(a: B, b: B, c: B): Unit = {
    Deduce(
        (a) |- (b | a | c)
        Proof(
            //PROOF GOES HERE
            1 ( a )     by Premise,
            2 ( b | a ) by OrI2(1),
            3 ( b | a | c ) by OrI1(2)

            //want: b | a | c
            //really (b | a) | c
            //need b | a on its own first
            //need to construct that OR last
        )
    )
}