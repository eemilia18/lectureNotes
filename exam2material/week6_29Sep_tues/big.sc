// #Sireum #Logika
import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

//(c ∧ n) → t, h ∧ ¬s, h ∧ ¬(s ∨ c) → p ⊢ (n ∧ ¬t) → p


@pure def big(c: B, n: B, t: B, h: B, s: B, p: B): Unit = {
  Deduce(
    ( (c & n) __>: t, h & !s, h & !(s | c) __>: p ) |- ( n & !t __>: p )
      Proof(
        1 ( (c & n) __>: t ) by Premise,
        2 ( h & !s ) by Premise,
        3 ( h & !(s | c) __>: p ) by Premise,

        4 ( h ) by AndE1(2),
        5 ( !s ) by AndE2(2),

        //use ImplyI to prove n & !t __>: p
        6 SubProof(
          7 Assume ( n & !t ),

          8 ( n ) by AndE1(7),
          9 ( !t ) by AndE2(7),

          //goal: !(s | c) so I can use premise 3
          //use NegI
          10 SubProof(
            11 Assume ( s | c ),

            //try using the OR statement on 11 with OrE
            12 SubProof(
              13 Assume ( s ),
              14 ( F ) by NegE(13, 5)

              //goal: contradiction
            ),
            15 SubProof(
              16 Assume ( c ),
              17 ( c & n ) by AndI(16, 8),
              18 ( t ) by ImplyE(1, 17),
              19 ( F ) by NegE(18, 9)

              //goal: contradiction
            ),
            20 ( F ) by OrE(11, 12, 15)

            //goal: contradiction 
          ),
          21 ( !(s | c) ) by NegI(10),
          22 ( h & !(s | c) ) by AndI(4, 21),
          23 ( p ) by ImplyE(3, 22)

          //goal: p
        ),
        24 ( n & !t __>: p ) by ImplyI(6)
    )
  )
}