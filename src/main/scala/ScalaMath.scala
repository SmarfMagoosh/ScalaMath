import scala.util.Random
import scala.annotation.tailrec

// Helpers
private val r = Random
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

  def prime: Func = this // TODO make abstract

  def integral: Func = this // TODO make abstract

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
}

private class Sum(f: Func, g: Func) extends Func {
  val _1: Func = f
  val _2: Func = g

  def of: Double => Double = (x: Double) => f(x) + g(x)

  override def simplify: Func = if f *= g then Scalar(f.scale + g.scale, f.asScalar._2).simplify else this
}

private class Product(f: Func, g: Func) extends Func {
  val _1: Func = f
  val _2: Func = g

  def of: Double => Double = (x: Double) => f(x) * g(x)

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

  def of: Double => Double = (x: Double) => f(g(x))

  override def simplify: Func = super.simplify // TODO implement
}

private class Tetr(f: Func, g: Func) extends Func {
  val _1: Func = f
  val _2: Func = g

  def of: Double => Double = (x: Double) => Math.pow(f(x), g(x))

  override def simplify: Func = super.simplify // TODO implement
}

private class Scalar(scalar: Double, f: Func) extends Func {
  override val funcType: String = f.funcType
  val _1: Double = scalar
  val _2: Func = f

  def of: Double => Double = (x: Double) => scalar * (f of x)

  override def simplify: Func = if scalar == 1 then f else super.simplify

  override def isScalar: Boolean = true

  override def as[T <: Func]: T = f.as[T]
}

private class Constant(constant: Double) extends Func {
  val _1: Double = constant

  def of: Double => Double = _ => constant
}

private class Poly(exp: Double) extends Func {
  val _1: Double = exp

  def of: Double => Double = (x: Double) => Math.pow(x, exp)
}

private class Exp(base: Double) extends Func {
  val _1: Double = base

  def of: Double => Double = (x: Double) => Math.pow(base, x)
}

private class Log(base: Double) extends Func {
  val _1: Double = base

  def of: Double => Double = (x: Double) => Math.log(x) / Math.log(base)
}

private class Sine extends Func {
  def of: Double => Double = (x: Double) => Math.sin(x)
}

private class Cosine extends Func {
  def of: Double => Double = (x: Double) => Math.cos(x)
}

private class Tangent extends Func {
  def of: Double => Double = (x: Double) => Math.tan(x)
}

private class Secant extends Func {
  def of: Double => Double = (x: Double) => 1.0 / Math.cos(x)
}

private class Cosecant extends Func {
  def of: Double => Double = (x: Double) => 1.0 / Math.sin(x)
}

private class Cotangent extends Func {
  def of: Double => Double = (x: Double) => 1.0 / Math.tan(x)
}

private class ArcSine extends Func {
  def of: Double => Double = (x: Double) => Math.asin(x)
}

private class ArcCosine extends Func {
  def of: Double => Double = (x: Double) => Math.acos(x)
}

private class ArcTangent extends Func {
  def of: Double => Double = (x: Double) => Math.atan(x)
}

private class ArcSecant extends Func {
  def of: Double => Double = (x: Double) => 1.0 / Math.acos(x)
}

private class ArcCosecant extends Func {
  def of: Double => Double = (x: Double) => 1.0 / Math.asin(x)
}

private class ArcCotangent extends Func {
  def of: Double => Double = (x: Double) => 1.0 / Math.atan(x)
}

private class HyperbolicSine extends Func {
  def of: Double => Double = (x: Double) => Math.sinh(x)
}

private class HyperbolicCosine extends Func {
  def of: Double => Double = (x: Double) => Math.cosh(x)
}

private class HyperbolicTangent extends Func {
  def of: Double => Double = (x: Double) => Math.tanh(x)
}

private class HyperbolicSecant extends Func {
  def of: Double => Double = (x: Double) => 1.0 / Math.cosh(x)
}

private class HyperbolicCosecant extends Func {
  def of: Double => Double = (x: Double) => 1.0 / Math.sinh(x)
}

private class HyperbolicCotangent extends Func {
  def of: Double => Double = (x: Double) => 1.0 / Math.tanh(x)
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

@main def main(): Unit = {
  val f: Func = (2*(x**0.5))*(0.25 * (x**3))
  println(f.getClass)
  println(f.funcType)
  println(f of pi)
}