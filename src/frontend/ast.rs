use crate::frontend::token::Token;

// Enums

#[derive(Debug, Clone, PartialEq)]
pub enum Statement {
    Let(LetStatement),
    Return(ReturnStatement),
    Expression(ExpressionStatement),
    Assign(AssignStatement),
    While(WhileStatement),
    Continue,
    Break,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Expression {
    Identifier(Token),
    IntegerLiteral(IntegerLiteralExpression),
    FloatLiteral(FloatLiteralExpression),
    Prefix(PrefixExpression),
    Infix(InfixExpression),
    Boolean(BooleanLiteralExpression),
    If(IfExpression),
    Function(FunctionLiteralExpression),
    Call(CallExpression),
    String(Token),
    Char(Token),
    Array(ArrayLiteralExpression),
    Hash(HashLiteralExpression),
    Index(IndexExpression),
}

// Statements

#[derive(Debug, Clone, PartialEq)]
pub struct LetStatement {
    pub token: Token,
    pub name: Token,
    pub value: Box<Expression>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ReturnStatement {
    pub token: Token,
    pub return_value: Box<Expression>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ExpressionStatement {
    pub token: Token,
    pub expression: Box<Expression>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct AssignStatement {
    pub token: Token,
    pub target: Box<Expression>,
    pub value: Box<Expression>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct WhileStatement {
    pub token: Token,
    pub condition: Box<Expression>,
    pub body: BlockStatement,
}

#[derive(Debug, Clone, PartialEq)]
pub struct BlockStatement {
    pub token: Token,
    pub statements: Vec<Statement>,
}

// Expressions

#[derive(Debug, Clone, PartialEq)]
pub struct IntegerLiteralExpression {
    pub token: Token,
    pub value: i64,
}

#[derive(Debug, Clone, PartialEq)]
pub struct FloatLiteralExpression {
    pub token: Token,
    pub value: f64,
}

#[derive(Debug, Clone, PartialEq)]
pub struct PrefixExpression {
    pub token: Token,
    pub right: Box<Expression>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct InfixExpression {
    pub token: Token,
    pub left: Box<Expression>,
    pub right: Box<Expression>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct BooleanLiteralExpression {
    pub token: Token,
    pub value: bool,
}

#[derive(Debug, Clone, PartialEq)]
pub struct IfExpression {
    pub token: Token,
    pub condition: Box<Expression>,
    pub consequence: BlockStatement,
    pub alternative: Option<BlockStatement>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct FunctionLiteralExpression {
    pub token: Token,
    pub parameters: Vec<Token>,
    pub body: BlockStatement,
    pub name: Option<Token>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct CallExpression {
    pub token: Token,
    pub function: Box<Expression>,
    pub arguments: Vec<Expression>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct IndexExpression {
    pub token: Token,
    pub left: Box<Expression>,
    pub index: Box<Expression>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ArrayLiteralExpression {
    pub token: Token,
    pub elements: Vec<Expression>,
}

#[derive(Debug, Clone)]
pub struct HashLiteralExpression {
    pub token: Token,
    pub pairs: Vec<(Expression, Expression)>,
}

impl PartialEq for HashLiteralExpression {
    fn eq(&self, other: &Self) -> bool {
        self.pairs == other.pairs
    }
}

// Program

pub struct Program {
    pub statements: Vec<Statement>,
}
