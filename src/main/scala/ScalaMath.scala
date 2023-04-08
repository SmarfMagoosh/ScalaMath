import scala.annotation.internal.Child
import scala.util.Random
import scala.annotation.tailrec

// Helpers
private val r: Random = Random
private def tests: List[Double] = for _ <- (0 to 50).toList yield r.nextInt(100) * r.nextDouble()

// Extensions for making Func arithmetic compatible with integers and doubles
extension [T <: Number](d: T)
  def +(f: Func): Func = (Constant(d.doubleValue()) + f).simplify
  def -(f: Func): Func = (Constant(d.doubleValue()) - f).simplify
  def *(f: Func): Func = Scalar(d.doubleValue(), f)
  def /(f: Func): Func = (Constant(d.doubleValue()) / f).simplify
  def **(f: Func): Func = if f == x then Exp(d.doubleValue()) else Comp(Exp(d.doubleValue()), f).simplify
  def ==(f: Func): Boolean = Constant(d.doubleValue()) == f

// definition of function
private abstract class Func {
  val funcType: String = this.getClass.toString.substring(6)
  val nonZero: Double = {
    @tailrec def findNonZero(d: Double = 0): Double = {
      if this.of(d) != 0 then d else if d >= 100 then Double.NaN else findNonZero(d + r.nextDouble())
    }
    findNonZero()
  }
  def scale: Double = if isScalar then asScalar._1 else 1

  def of: Double => Double

  def prime: Func

  def integral: Func

  def simplify: Func = this

  def apply(x: Double): Double = this of x

  def apply(f: Func): Func = {
    if f == x then this
    else if f.isConstant then Constant(this of f.as[Constant]._1)
    else if this.isInverseOf(f) then x
    else Comp(this, f).simplify
  }

  def +(d: Double): Func = Sum(this, Constant(d)).simplify

  def +(f: Func): Func = Sum(this, f).simplify

  def -(d: Double): Func = Sum(this, Constant(-d)).simplify

  def -(f: Func): Func = Sum(this, Scalar(-1, f)).simplify

  def *(d: Double): Func = Scalar(d, this).simplify

  def *(f: Func): Func = Product(this, f).simplify

  def /(d: Double): Func = Scalar(1.0 / d, this).simplify

  def /(f: Func): Func = Product(this, f ** -1).simplify

  def **(d: Double): Func = if this == x then Poly(d) else Comp(Poly(d), this).simplify

  def **(f: Func): Func = Tetr(this, f).simplify

  def ==(f: Func): Boolean = tests.count(Sum(this, Scalar(-1, f))(_).abs > 0.00000001) == 0

  def !=(f: Func): Boolean = !(this == f)

  def ==(d: Double): Boolean = this == Constant(d)

  def !=(d: Double): Boolean = this != Constant(d)

  def *=(f: Func): Boolean = f == Scalar(f.of(nonZero) / this.of(nonZero), this)

  def *=(d: Double): Boolean = this *= Constant(d)

  def !*=(f: Func): Boolean = !(this *= f)

  def !*=(d: Double): Boolean = !(this *= d)

  def isInverseOf(f: Func): Boolean = tests.count(Sum(Comp(this, f), Scalar(-1, x))(_).abs > 0.00000001) == 0

  def findScalar(f: Func): Double = if this *= f then f(nonZero) / this (nonZero) else Double.NaN

  def isSum: Boolean = this.funcType == "Sum"

  def isProduct: Boolean = this.funcType == "Product"

  def isComp: Boolean = this.funcType == "Comp"

  def isTetr: Boolean = this.funcType == "Tetr"

  def isScalar: Boolean = false

  def isConstant: Boolean = this.funcType == "Constant"

  def isLine: Boolean = this.funcType == "Line"

  def isPoly: Boolean = this.funcType == "Poly"

  def isExp: Boolean = this.funcType == "Exp"

  def isLog: Boolean = this.funcType == "Log"

  def isSine: Boolean = this.funcType == "Sine"

  def isCosine: Boolean = this.funcType == "Cosine"

  def isTangent: Boolean = this.funcType == "Tangent"

  def isSecant: Boolean = this.funcType == "Secant"

  def isCosecant: Boolean = this.funcType == "Cosecant"

  def isCotangent: Boolean = this.funcType == "Cotangent"

  def isArcSine: Boolean = this.funcType == "ArcSine"

  def isArcCosine: Boolean = this.funcType == "ArcCosine"

  def isArcTangent: Boolean = this.funcType == "ArcTangent"

  def isArcSecant: Boolean = this.funcType == "ArcSecant"

  def isArcCosecant: Boolean = this.funcType == "ArcCosecant"

  def isArcCotangent: Boolean = this.funcType == "ArcCotangent"

  def isHyperbolicSine: Boolean = this.funcType == "HyperbolicSine"

  def isHyperbolicCosine: Boolean = this.funcType == "HyperbolicCosine"

  def isHyperbolicTangent: Boolean = this.funcType == "HyperbolicTangent"

  def isHyperbolicSecant: Boolean = this.funcType == "HyperbolicSecant"

  def isHyperbolicCosecant: Boolean = this.funcType == "HyperbolicCosecant"

  def isHyperbolicCotangent: Boolean = this.funcType == "HyperbolicCotangent"

  def as[T <: Func]: T = this.asInstanceOf[T]
  def asScalar: Scalar = this.asInstanceOf[Scalar]
}

private class Erf extends Func {
  def of: Double => Double = _ => Double.NaN
  def prime: Func = this
  def integral: Func = this
}

private class Sum(f: Func, g: Func) extends Func {
  val _1: Func = f
  val _2: Func = g

  def of: Double => Double = (d: Double) => f(d) + g(d)
  def prime: Func = Sum(f.prime, g.prime).simplify
  def integral: Func = Sum(f.integral, g.integral).simplify

  override def simplify: Func = if f *= g then Scalar(f.scale + g.scale, f.asScalar._2).simplify else this
}

private class Product(f: Func, g: Func) extends Func {
  val _1: Func = f
  val _2: Func = g

  def of: Double => Double = (d: Double) => f(d) * g(d)
  def prime: Func = Sum(Product(f.prime, g).simplify, Product(f, g.prime).simplify).simplify
  def integral: Func = Erf() // TODO try to solve

  override def simplify: Func = {
    if f.isPoly && g.isPoly then Scalar(f.scale * g.scale, x**(f.as[Poly]._1 + g.as[Poly]._1)).simplify
    else if f.isExp && g.isExp then
      if f.as[Exp]._1 == g.as[Exp]._1 then Scalar(f.scale * g.scale, Exp(f.as[Exp]._1 + g.as[Exp]._1)).simplify
      else super.simplify
    else if f.funcType == g.funcType then
      if f.isScalar then Scalar(f.scale * g.scale, Comp(Poly(2), f.asScalar._2))
      else Scalar(g.scale, Comp(Poly(2), f))
    else super.simplify
  }
}

private class Comp(f: Func, g: Func) extends Func {
  val _1: Func = f
  val _2: Func = g

  def of: Double => Double = (d: Double) => f(g(d))
  def prime: Func = Product(Comp(f.prime, g), g.prime)
  def integral: Func = Erf() // TODO solve

  override def simplify: Func = {
    if f.isPoly && g.isPoly then Scalar(f.scale * Math.pow(g.scale, f.as[Poly]._1), Poly(f.as[Poly]._1 * g.as[Poly]._1))
    else if f.isLog then
      if g.isPoly then Scalar(f.scale * g.as[Poly]._1, Log(f.as[Log]._1))
      else if g.isExp then Scalar(f.scale * Log(f.as[Log]._1)(g.as[Exp]._1), x)
      else if g.isTetr then Product(f.scale * g.as[Tetr]._2, Log(f.as[Log]._1)(g.as[Tetr]._1))
      else super.simplify
    else if f.isExp && g.isLog then x ** (1 / ln(g.as[Log]._1))
    else super.simplify
  }
}

private class Tetr(f: Func, g: Func) extends Func {
  val _1: Func = f
  val _2: Func = g

  def of: Double => Double = (d: Double) => Math.pow(f(d), g(d))
  def prime: Func = Erf() // TODO solve
  def integral: Func = Erf() // TODO solve

  override def simplify: Func = if f *= 1 then f(1) ** g else if g *= 1 then f ** g(1) else super.simplify
}

private class Scalar(scalar: Double, f: Func) extends Func {
  override val funcType: String = f.funcType
  val _1: Double = scalar
  val _2: Func = f

  def of: Double => Double = (x: Double) => scalar * (f of x)

  def prime: Func = scalar * f.prime

  def integral: Func = scalar * f.integral

  override def simplify: Func = if scalar == 1 then f else super.simplify

  override def isScalar: Boolean = true

  override def as[T <: Func]: T = f.as[T]
}

private class Constant(constant: Double) extends Func {
  val _1: Double = constant

  def of: Double => Double = _ => constant

  def prime: Func = Constant(0)

  def integral: Func = constant * x
}

private class Poly(exp: Double) extends Func {
  val _1: Double = exp

  def of: Double => Double = (x: Double) => Math.pow(x, exp)

  def prime: Func = exp * Poly(exp - 1)

  def integral: Func = (1.0 / (exp + 1)) * Poly(exp + 1)
}

private class Exp(base: Double) extends Func {
  val _1: Double = base

  def of: Double => Double = (x: Double) => Math.pow(base, x)

  def prime: Func = Erf() // TODO solve

  def integral: Func = Erf() // TODO solve
}

private class Log(base: Double) extends Func {
  val _1: Double = base

  def of: Double => Double = (x: Double) => Math.log(x) / Math.log(base)

  def prime: Func = Erf() // TODO solve

  def integral: Func = Erf() // TODO solve
}

private class Sine extends Func {
  def of: Double => Double = (x: Double) => Math.sin(x)

  def prime: Func = Erf() // TODO solve

  def integral: Func = Erf() // TODO solve
}

private class Cosine extends Func {
  def of: Double => Double = (x: Double) => Math.cos(x)

  def prime: Func = Erf() // TODO solve

  def integral: Func = Erf() // TODO solve
}

private class Tangent extends Func {
  def of: Double => Double = (x: Double) => Math.tan(x)

  def prime: Func = Erf() // TODO solve

  def integral: Func = Erf() // TODO solve
}

private class Secant extends Func {
  def of: Double => Double = (x: Double) => 1.0 / Math.cos(x)

  def prime: Func = Erf() // TODO solve

  def integral: Func = Erf() // TODO solve
}

private class Cosecant extends Func {
  def of: Double => Double = (x: Double) => 1.0 / Math.sin(x)

  def prime: Func = Erf() // TODO solve

  def integral: Func = Erf() // TODO solve
}

private class Cotangent extends Func {
  def of: Double => Double = (x: Double) => 1.0 / Math.tan(x)

  def prime: Func = Erf() // TODO solve

  def integral: Func = Erf() // TODO solve

}

private class ArcSine extends Func {
  def of: Double => Double = (x: Double) => Math.asin(x)

  def prime: Func = Erf() // TODO solve

  def integral: Func = Erf() // TODO solve
}

private class ArcCosine extends Func {
  def of: Double => Double = (x: Double) => Math.acos(x)

  def prime: Func = Erf() // TODO solve

  def integral: Func = Erf() // TODO solve
}

private class ArcTangent extends Func {
  def of: Double => Double = (x: Double) => Math.atan(x)

  def prime: Func = Erf() // TODO solve

  def integral: Func = Erf() // TODO solve
}

private class ArcSecant extends Func {
  def of: Double => Double = (x: Double) => 1.0 / Math.acos(x)

  def prime: Func = Erf() // TODO solve

  def integral: Func = Erf() // TODO solve
}

private class ArcCosecant extends Func {
  def of: Double => Double = (x: Double) => 1.0 / Math.asin(x)

  def prime: Func = Erf() // TODO solve

  def integral: Func = Erf() // TODO solve
}

private class ArcCotangent extends Func {
  def of: Double => Double = (x: Double) => 1.0 / Math.atan(x)

  def prime: Func = Erf() // TODO solve

  def integral: Func = Erf() // TODO solve
}

private class HyperbolicSine extends Func {
  def of: Double => Double = (x: Double) => Math.sinh(x)

  def prime: Func = Erf() // TODO solve

  def integral: Func = Erf() // TODO solve
}

private class HyperbolicCosine extends Func {
  def of: Double => Double = (x: Double) => Math.cosh(x)

  def prime: Func = Erf() // TODO solve

  def integral: Func = Erf() // TODO solve
}

private class HyperbolicTangent extends Func {
  def of: Double => Double = (x: Double) => Math.tanh(x)

  def prime: Func = Erf() // TODO solve

  def integral: Func = Erf() // TODO solve
}

private class HyperbolicSecant extends Func {
  def of: Double => Double = (x: Double) => 1.0 / Math.cosh(x)

  def prime: Func = Erf() // TODO solve

  def integral: Func = Erf() // TODO solve
}

private class HyperbolicCosecant extends Func {
  def of: Double => Double = (x: Double) => 1.0 / Math.sinh(x)

  def prime: Func = Erf() // TODO solve

  def integral: Func = Erf() // TODO solve
}

private class HyperbolicCotangent extends Func {
  def of: Double => Double = (x: Double) => 1.0 / Math.tanh(x)

  def prime: Func = Erf() // TODO solve

  def integral: Func = Erf() // TODO solve
}

val ln: Log = Log(Math.E)
val lg: Log = Log(2)
val log: Double => Log = (d: Double) => Log(d)

val x = Poly(1)

val sin = Sine()
val cos = Cosine()
val tan = Tangent()
val sec = Secant()
val csc = Cosecant()
val cot = Cotangent()

val arcsin = ArcSine()
val arccos = ArcCosine()
val arctan = ArcTangent()
val arcsec = ArcSecant()
val arccsc = ArcCosecant()
val arccot = ArcCotangent()

val sinh = HyperbolicSine()
val cosh = HyperbolicCosine()
val tanh = HyperbolicTangent()
val sech = HyperbolicSecant()
val csch = HyperbolicCosecant()
val coth = HyperbolicCotangent()

val e = Math.E
val pi = Math.PI
val phi = (1 + Math.sqrt(5)) / 2
val tau = Math.TAU

// Matrices

// Probability

// solve linear equations
