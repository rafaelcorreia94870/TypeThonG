from lark import Lark,Transformer,Discard
from lark.tree import pydot__tree_to_png
from lark.visitors import Interpreter
#dicionario com as chaves como variavel, scope e o seu valor os valores que lhe foram atribuidos

grammar = r'''
    // Regras Sintaticas - typethong script.tt
    ?start: _NL* content*

    content: declaration (_NL)*
           | attribution (_NL)*
           | cycle
           | write (_NL)*
           | read (_NL)*
           | condition
           | add_elem
           | RETURN expression (_NL)*
           | expression
           | function

    function: (type|T_VOID) ID LCP ( | type ID (COMMA type ID)* ) RCP body

    declaration: type ID (EQUALS expression)?

    attribution: variable EQUALS expression
    
    body: COLON _NL+ _INDENT content+ _DEDENT

    variable: ID access*

    access: LSP INT ( | COLON ( |INT)) RSP
          | LSP COLON INT RSP
          | DOT ID

    type: T_INT
        | T_SET LSP type RSP
        | T_ARRAY LSP type RSP
        | T_TUPLE LSP type (COMMA type)+ RSP
        | T_STRING
        | T_LIST LSP type RSP

    expression : priority_expr
               | priority_expr relational_op priority_expr
                
    relational_op : ISEQ | NE | LT | LE | GT | GE
    
    priority_expr : term
        | priority_expr addOp term
     
    term : factor
         | term multOp factor
    
    addOp : PLUS | MINUS | OR
    
    multOp : TIMES | DIVIDE | AND | MOD | POW
    
    factor : INT
           | STRING
           | LP expression RP
           | functionCall
           | uniOp factor
           | ID
           | listDeclaration
           
     uniOp : PLUS | MINUS | NOT
     
     functionCall : ID LCP ( | expression (COMMA expression)*) RCP
     listDeclaration : LSP (expression (COMMA expression)*)? RSP
    

    condition: IF expression body (ELIF expression body)* (ELSE body)?
             | MATCH variable COLON _NL _INDENT (WITH expression body)+ _DEDENT

    write: PRINT LCP expression RCP

    read: READ LCP RCP

    cycle: DO body WHILE expression _NL+
         | WHILE expression body
         | FOR ID IN iterable body

    iterable: RANGE LCP INT (COMMA INT)? RCP
            | variable

    add_elem : variable COLON variable

    // Regras Lexicográficas
    ID: /[a-zA-Z]\w*/
    INT: /-?\d+/
    STRING: /("|').*?("|')/

    LCP: /\(/
    RCP: /\)/
    LSP: "["
    RSP: "]"
    COMMA: ","
    COLON: ":"
    DOT: "."

    PLUS: "+"
    MINUS: "-"
    TIMES: "*"
    DIVIDE: "/"
    POW: "^"
    MOD: "%"
    LT: "<"
    GT: ">"
    EQUALS: "="
    ISEQ: "=="
    NE: "!="
    LE: "<="
    GE: ">="
    AND: /(and|\&\&)/
    OR: /(or|\|\|)/
    NOT: /(not|\!)/

    T_INT: "int"
    T_SET: "set"
    T_ARRAY: "array"
    T_TUPLE: "tuple"
    T_STRING: "string"
    T_LIST: "list"
    T_VOID: "void"

    RETURN: "return"
    IF: "if"
    ELIF: "elif"
    ELSE: "else"
    DO: "do"
    WHILE: "while"
    FOR: "for"
    IN: "in"
    RANGE: "range"
    READ: "read"
    WRITE: "write"
    MATCH: "match"
    WITH: "with"
    PRINT: "print"

    %import common.WS_INLINE
    %declare _INDENT _DEDENT
    %ignore WS_INLINE

    _NL: /(\r?\n[\t ]*)+/
'''

def relationOperation(op, a, b):
    op = op.value
    if op == "==":
        return a == b
    elif op == "!=":
        return a != b
    elif op == "<":
        return a < b
    elif op == "<=":
        return a <= b
    elif op == ">":
        return a > b
    elif op == ">=":
        return a >= b
    
def addOperation(op, a, b):
    op = op.type
    if op == "PLUS":
        return a + b
    elif op == "MINUS":
        return a - b
    elif op == "OR":
        return a or b
    
def multOperation(op, a, b):
    op = op.type
    if op == "TIMES":
        return a * b
    elif op == "DIVIDE":
        return a / b
    elif op == "AND":
        return a and b
    elif op == "MOD":
        return a % b
    elif op == "POW":
        return a ** b

class DicInterpreter(Interpreter):
    def __init__(self):
        self.dic = {}
        self.scope = ""
    def start(self,tree):
        self.visit_children(tree)
        return self.dic
    
    def content(self,tree):
        self.visit_children(tree)

    def function(self,tree):
        self.scope = self.visit(tree.children[1])
        self.visit_children(tree)
        self.scope = ""

    def declaration(self,tree):
        name = self.visit(tree.children[1])
        key = (self.scope, name)
        type = self.visit(tree.children[0])
        if key not in self.dic:
            self.dic[key] = (type,[])
        else:
            print(f"Error: Variable {name} already declared")

        if len(tree)>2:
            #verificar tipo da expressão depois
            self.dic[key][1].append(self.visit(tree.children[3]))
    
    def atribuition(self,tree):
        name = self.visit(tree.children[0])
        key = (self.scope, name)
        
        if key in self.dic:
            #verificar tipo da expressão depois
            self.dic[key][1].append(self.visit(tree.children[2]))
        else:
            print(f"Error: Variable {name} not declared")
    
    def body(self,tree):
        self.visit_children(tree)

    def variable(self,tree):
        return self.visit(tree.children[0])
    
    #def access(self,tree):
    #    return self.visit(tree.children[0])

    def type(self,tree):
        result = self.visit_children(tree)
        if len(result) == 1:
            return result[0]
        else:
            return (result[0], result[1:])
        
    def expression(self,tree):
        result = self.visit_children(tree)
        if len(result) == 1:
            return result[0]
        else:
            return relationOperation(result[1], result[0], result[2])

        
    def relational_op(self,tree):
        return self.visit(tree.children[0])
    
    def priority_expr(self,tree):
        result = self.visit_children(tree)
        if len(result) == 1:
            return result[0]
        else:
            return addOperation(result[1], result[0], result[2])

    def term(self,tree):
        result = self.visit_children(tree)
        if len(result) == 1:
            return result[0]
        else:
            return multOperation(result[1], result[0], result[2])

    def add_op(self,tree):
        return self.visit(tree.children[0])
    
    def mult_op(self,tree):
        return self.visit(tree.children[0])
    
    def factor(self,tree):
        result = self.visit_children(tree)
        if len(result) == 1:
            #tratar se for functionCall, problema no functionCall em si
            return result[0]
        else:
            return result[1](result[0])

    def uni_op(self,tree):
        return self.visit(tree.children[0])
    
    def function_call(self,tree):
        pass

    def list_declaration(self,tree):
        pass

    def condition(self,tree):
        pass

    def write(self,tree):
        pass

    def read(self,tree):
        pass

    def cycle(self,tree):
        pass

    def iterable(self,tree):
        pass

    def add_elem(self,tree):
        pass

    


    
    