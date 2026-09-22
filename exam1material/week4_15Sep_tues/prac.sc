// #Sireum #Logika

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

@pure def prac(a: B, b: B, c: B, p: B, q: B, r: B, s: B, t: B): Unit = {
  Deduce(
    ( b & (s | a), s __>: b __>: p, a & b __>: t, p | t __>: q __>: r, b | c __>: q ) |- ( r )
      Proof(
      1 (  b & (s | a)   ) by Premise,
      2 (  s __>: b __>: p   ) by Premise,
      3 ( a & b __>: t ) by Premise,
      4 ( p | t __>: q __>: r ) by Premise,
      5 ( b | c __>: q ) by Premise,
      
      //break apart premise 1
      6 ( b ) by AndE1(1),
      7 ( s | a ) by AndE2(1),

      //try OrE on s | a
      8 SubProof(
        9 Assume(s),
        10 ( b __>: p ) by ImplyE(2, 9),
        11 ( p ) by ImplyE(10, 6),
        12 ( p | t ) by OrI1(11),
        13 ( q __>: r ) by ImplyE(4, 12),
        14 ( b | c ) by OrI1(6),
        15 ( q ) by ImplyE(5, 14),
        16 ( r ) by ImplyE(13, 15)

        //if I can get q, can get r
        //goal: r
      ),
      17 SubProof(
        18 Assume ( a ),
        19 ( a & b ) by AndI(18, 6),
        20 ( t ) by ImplyE(3, 19),
        21 ( p | t ) by OrI2(20),
        22 ( q __>: r ) by ImplyE(4, 21),
        23 ( b | c ) by OrI1(6),
        24 ( q ) by ImplyE(5, 23),
        25 ( r ) by ImplyE(22, 24)
        //goal: r
      ),
      26 ( r ) by OrE(7, 8, 17)
      //subproof with a, goal is r
    )
      //goal is r
  )
}