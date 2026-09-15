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
      
      
  )
}