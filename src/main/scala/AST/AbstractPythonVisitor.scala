package main.scala.AST

import parser.PythonParser._
import parser.PythonBaseVisitor 


class AbstractPythonVisitor extends PythonBaseVisitor[Node] {

  override def visitExpression_1(ctx: Expression_1Context): Node = super.visitExpression_1(ctx)
  override def visitExpression_2(ctx: Expression_2Context): Node = super.visitExpression_2(ctx)
  override def visitExpression_3(ctx: Expression_3Context): Node = super.visitExpression_3(ctx)
  override def visitExpression_4(ctx: Expression_4Context): Node = super.visitExpression_4(ctx)
  override def visitExpression_5(ctx: Expression_5Context): Node = super.visitExpression_5(ctx)
  override def visitExpression_6(ctx: Expression_6Context): Node = super.visitExpression_6(ctx)
  override def visitExpression_7(ctx: Expression_7Context): Node = super.visitExpression_7(ctx)
  override def visitExpression_8(ctx: Expression_8Context): Node = super.visitExpression_8(ctx)
  override def visitExpression_9(ctx: Expression_9Context): Node = super.visitExpression_9(ctx)
  override def visitExpression_10(ctx: Expression_10Context): Node = super.visitExpression_10(ctx)
  override def visitExpression_11(ctx: Expression_11Context): Node = super.visitExpression_11(ctx)
  override def visitExpression_12(ctx: Expression_12Context): Node = super.visitExpression_12(ctx)
  override def visitExpression_13(ctx: Expression_13Context): Node = super.visitExpression_13(ctx)
  override def visitExpression_14(ctx: Expression_14Context): Node = super.visitExpression_14(ctx)
  override def visitExpression_15(ctx: Expression_15Context): Node = super.visitExpression_15(ctx)
  override def visitExpression_16(ctx: Expression_16Context): Node = super.visitExpression_16(ctx)
  override def visitExpression_17(ctx: Expression_17Context): Node = super.visitExpression_17(ctx)
  override def visitExpression_18(ctx: Expression_18Context): Node = super.visitExpression_18(ctx)
  override def visitExpression_19(ctx: Expression_19Context): Node = super.visitExpression_19(ctx)
  override def visitExpression_20(ctx: Expression_20Context): Node = super.visitExpression_20(ctx)
  override def visitExpression_21(ctx: Expression_21Context): Node = super.visitExpression_21(ctx)
  override def visitExpression_22(ctx: Expression_22Context): Node = super.visitExpression_22(ctx)

  
  override def visitCompound_statement_1(ctx: Compound_statement_1Context): Node = super.visitCompound_statement_1(ctx)
  override def visitCompound_statement_2(ctx: Compound_statement_2Context): Node = super.visitCompound_statement_2(ctx)
  override def visitCompound_statement_3(ctx: Compound_statement_3Context): Node = super.visitCompound_statement_3(ctx)
  override def visitCompound_statement_4(ctx: Compound_statement_4Context): Node = super.visitCompound_statement_4(ctx)

  override def visitSubscription(ctx: SubscriptionContext ): Node = super.visitSubscription(ctx)

  override def visitSmall_statement_1(ctx: Small_statement_1Context ): Node = super.visitSmall_statement_1(ctx)
  override def visitSmall_statement_2(ctx: Small_statement_2Context ): Node = super.visitSmall_statement_2(ctx)
  override def visitSmall_statement_3(ctx: Small_statement_3Context ): Node = super.visitSmall_statement_3(ctx)
  override def visitSmall_statement_4(ctx: Small_statement_4Context ): Node = super.visitSmall_statement_4(ctx)

  override def visitSmall_statement_list(ctx: Small_statement_listContext ): Node = super.visitSmall_statement_list(ctx)
  override def visitModule(ctx: ModuleContext ): Node = super.visitModule(ctx)
  override def visitFuncdef(ctx: FuncdefContext ): Node = super.visitFuncdef(ctx)
  override def visitStatement_list(ctx: Statement_listContext ): Node = super.visitStatement_list(ctx)
  override def visitKey_datum_list(ctx: Key_datum_listContext ): Node = super.visitKey_datum_list(ctx)
  override def visitWhile_stmt(ctx: While_stmtContext ): Node = super.visitWhile_stmt(ctx)
  override def visitId_list(ctx: Id_listContext ): Node = super.visitId_list(ctx)

  override def visitStatement_1(ctx: Statement_1Context ): Node = super.visitStatement_1(ctx)
  override def visitStatement_2(ctx: Statement_2Context ): Node = super.visitStatement_2(ctx)

  override def visitIfInstr(ctx: IfInstrContext ): Node = super.visitIfInstr(ctx)
  override def visitExpr_list_comma(ctx: Expr_list_commaContext ): Node = super.visitExpr_list_comma(ctx)
  override def visitKey_datum(ctx: Key_datumContext ): Node = super.visitKey_datum(ctx)
  override def visitClassdef(ctx: ClassdefContext ): Node = super.visitClassdef(ctx)
  override def visitProgram(ctx: ProgramContext ): Node = super.visitProgram(ctx)

  override def visitTarget_1(ctx: Target_1Context ): Node = super.visitTarget_1(ctx)
  override def visitTarget_2(ctx: Target_2Context ): Node = super.visitTarget_2(ctx)
  override def visitTarget_3(ctx: Target_3Context ): Node = super.visitTarget_3(ctx)

  override def visitSuite(ctx: SuiteContext ): Node = super.visitSuite(ctx)
  override def visitSimple_statement(ctx: Simple_statementContext ): Node = super.visitSimple_statement(ctx)
  override def visitExpr_list(ctx: Expr_listContext ): Node = super.visitExpr_list(ctx)

}
