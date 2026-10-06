// #Sireum #Logika

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._


//Complete the following natural deduction proof.
//When you are finished, do a Logika check.
//Your file should say "Logika verified".

//p ∨ q, p → a ∨ b, q → a ∨ b, a → c, b → c ⊢ c

@pure def hw4_prob1(p: B, q: B, a: B, b: B, c: B): Unit = {
  Deduce(
    (p | q, p __>: a | b, q __>: a | b, a __>: c, b __>: c) |- ( c )
      Proof(
        1 (  p | q             ) by Premise,
        2 (  p __>: a | b         ) by Premise,
        3 (  q __>: a | b         ) by Premise,
        4 (  a __>: c             ) by Premise,
        5 (  b __>: c             ) by Premise,
        6 SubProof(
          7 Assume (  p  ),
          8 (  a | b           ) by ImplyE(2, 7),
          9 SubProof(
            10 Assume(  a  ),
            11 (  c            ) by ImplyE(4, 10)
          ),
          12 SubProof(
            13 Assume (  b  ),
            14 (  c            ) by ImplyE(5, 13)
          ),
          15 (  c              ) by OrE(8,9,12)
        ),
      16 SubProof(
        17 Assume (  q  ),
        18 (  a | b            ) by ImplyE(3, 17),
        19 SubProof(
          20 Assume(  a  ),
          21 (  c              ) by ImplyE(4, 20)
        ),
        22 SubProof(
          23 Assume (  b  ),
          24 (  c              ) by ImplyE(5, 23)
        ),
        25 (  c                ) by OrE(18,19,22)
      ),
      26 (  c                  ) by OrE(1,6,16)
    )
  )
}
