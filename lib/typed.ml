include Poulet4.Typed

type direction = Poulet4.Typed.direction

type coq_P4Type = Types.tag Poulet4.Typed.coq_P4Type
type coq_FieldType = Types.P4string.t * coq_P4Type
type coq_FunctionType = (Info.t * Types.Annotation.t list) Poulet4.Typed.coq_FunctionType
type coq_ControlType = (Info.t * Types.Annotation.t list) Poulet4.Typed.coq_ControlType
type coq_P4Parameter = (Info.t * Types.Annotation.t list) Poulet4.Typed.coq_P4Parameter
type coq_StmtContext = (Info.t * Types.Annotation.t list) Poulet4.Typed.coq_StmtContext
type coq_DeclContext = (Info.t * Types.Annotation.t list) Poulet4.Typed.coq_DeclContext

let eq_dir d1 d2 =
  match d1, d2 with
  | In, In
  | Out, Out
  | InOut, InOut
  | Directionless, Directionless -> true
  | _ -> false

let expr_ctxt_of_stmt_ctxt (s: coq_StmtContext) : coq_ExprContext =
  match s with
  | StmtCxFunction ret -> ExprCxFunction
  | StmtCxAction -> ExprCxAction
  | StmtCxParserState -> ExprCxParserState
  | StmtCxApplyBlock -> ExprCxApplyBlock

let expr_ctxt_of_decl_ctxt (s: coq_DeclContext) : coq_ExprContext =
  match s with
   | DeclCxTopLevel -> ExprCxConstant
   | DeclCxNested -> ExprCxDeclLocals
   | DeclCxStatement c -> expr_ctxt_of_stmt_ctxt c

type 'a info = 'a Types.info

module Annotation = Types.Annotation
