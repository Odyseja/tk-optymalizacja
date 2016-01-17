package simplifier

import javax.security.auth.login.FailedLoginException

import AST._

// to implement
// avoid one huge match of cases
// take into account non-greedy strategies to resolve cases with power laws
object Simplifier {

  //def simplify(node: Node) = node

  def simplify(node: Node): Node = node match {
    case BinExpr(op, leftNode, rightNode) => {
      val left: Node = simplify(leftNode)
      val right: Node = simplify(rightNode)

      op match {
        case "and" => and(left, right)
        case "or" => or(left, right)
        case "==" => equals(left, right)
        case "<=" => lowerOrEquals(left, right)
        case ">=" => greaterOrEquals(left, right)
        case "<" => lower(left, right)
        case ">" => greater(left, right)
        case _ => evaluateExpression(op, left, right)
      }

    }
    case Unary(op, expr) => {
      val simplyExpr: Node = simplify(expr)
      op match {
        case _ => Unary(op, simplyExpr)
      }

    }
    case NodeList(list) => NodeList(list.map{case f => simplify(f)})
    case KeyDatumList(list) => KeyDatumList(list.map{case f => simplifyKeyDatum(f)})
    case ElemList(list) => ElemList(list.map{case f => simplify(f)})
    case IfInstr(cond, body) => IfInstr(simplify(cond), simplify(body))
    case IfElseInstr(cond, myIf, myElse) => IfElseInstr(simplify(cond), simplify(myIf), simplify(myElse))
    case Assignment(variable, assign) => Assignment(variable, simplify(assign))
    case ReturnInstr(expr) => ReturnInstr(simplify(expr))
    case PrintInstr(expr) => PrintInstr(simplify(expr))
    case WhileInstr(cond, body) => WhileInstr(simplify(cond), simplify(body))
    case Subscription(primary, expression_list) => Subscription(simplify(primary), simplify(expression_list))
    case GetAttr(expr, attr) => GetAttr(simplify(expr), attr)
    case KeyDatum(key, datum) => KeyDatum(simplify(key), simplify(datum))
    case FunCall(name, args) => FunCall(name, simplify(args))
    case FunDef(name, formal_args, body) => FunDef(name, simplify(formal_args), simplify(body))
    case ClassDef(name, inherit_list, suit) => ClassDef(name, simplify(inherit_list), simplify(suit))
    case _ => node
  }
  //BinaryExpression helpers
  def and(left: Node, right: Node):Node = (left, right) match {
    case(_, FalseConst()) => FalseConst()
    case(FalseConst(), _) => FalseConst()
    case(TrueConst(), TrueConst()) => TrueConst()
    case(_, _) => BinExpr("and", left, right)
  }
  def or(left: Node, right: Node):Node = (left, right) match {
    case(_, TrueConst()) => TrueConst()
    case(TrueConst(), _) => TrueConst()
    case(FalseConst(), FalseConst()) => FalseConst()
    case(_, _) => BinExpr("or", left, right)
  }
  def equals(left: Node, right: Node):Node = (left, right) match {
    case(_, _) => BinExpr("==", left, right)
  }
  def lowerOrEquals(left: Node, right: Node):Node = (left, right) match {
    case(_, _) => BinExpr("<=", left, right)
  }
  def greaterOrEquals(left: Node, right: Node):Node = (left, right) match {
    case(_, _) => BinExpr(">=", left, right)
  }
  def lower(left: Node, right: Node):Node = (left, right) match {
    case(_, _) => BinExpr("<", left, right)
  }
  def greater(left: Node, right: Node):Node = (left, right) match {
    case(_, _) => BinExpr(">", left, right)
  }
  def evaluateExpression(op: String, left: Node, right: Node):Node = (op, left, right) match {
    case _ => BinExpr(op, left, right)
  }

  //Needed returning KeyDatum instead of Node
  def simplifyKeyDatum(keyDatum: Node): KeyDatum = keyDatum match {
    case KeyDatum(key, datum) => KeyDatum(simplify(key), simplify(datum))
    case _ => KeyDatum(StringConst("error"), StringConst("error"))
  }
}
