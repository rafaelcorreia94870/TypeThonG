import pprint
from lark import Lark,Transformer,Discard
from lark.tree import pydot__tree_to_png
from lark.visitors import Interpreter
from lark.indenter import Indenter
from collections import Counter
#dicionario com as chaves como variavel, scope e o seu valor os valores que lhe foram atribuidos

grammar = r'''
    // Regras Sintaticas - typethong script.tt
    start: _NL* content*

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
        | T_VOID

    expression: priority_expr
              | priority_expr relational_op priority_expr
                
    relational_op: ISEQ | NE | LT | LE | GT | GE
    
    priority_expr : term
        | priority_expr add_op term
     
    term : factor
         | term mult_op factor
    
    add_op : PLUS | MINUS | OR
    
    mult_op : TIMES | DIVIDE | AND | MOD | POW
    
    factor : INT
           | STRING
           | LCP expression RCP
           | function_call
           | uni_op factor
           | ID                 -> factor_id
           | list_declaration
           
    uni_op : PLUS | MINUS | NOT
     
    function_call : ID LCP ( | expression (COMMA expression)*) RCP
    list_declaration : LSP (expression (COMMA expression)*)? RSP

    condition: IF expression body (ELIF expression body)* (ELSE body)?
             | MATCH variable COLON _NL _INDENT (WITH expression body)+ _DEDENT

    write: PRINT LCP expression RCP

    read: READ LCP RCP

    cycle: DO body WHILE expression _NL+
         | WHILE expression body -> while_loop
         | FOR ID IN iterable body -> for_loop

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
    if op == "PLUS":
        return a + b
    elif op == "MINUS":
        return a - b
    elif op == "OR":
        return a or b
    
def multOperation(op, a, b):
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
    
class TreeIndenter(Indenter):
    NL_type = '_NL'
    OPEN_PAREN_types = []
    CLOSE_PAREN_types = []
    INDENT_type = '_INDENT'
    DEDENT_type = '_DEDENT'
    tab_len = 4

class DicInterpreter(Interpreter):
    def __init__(self):
        self.dic = {}
        self.scope = ""
    
    # vars= [(ID,scope,type),...] 
    # erros = [lista de erros]
    # tipos[Tipo de dados] = [(id,scope),..]
    # instrucao = {total: int, atribuicoes: int, leitura: int, escrita, int, condicionais: int, cíclicas : int}
    # mausif : in
    # listaif = [strings,..] 
    def start(self,tree):
        self.info = {"vars": [], "erros": [], "tipos": {}, "instrucao": Counter(), "mausif": [], "listaif": []}
        self.visit_children(tree)
        for (name, scope), (type, attr) in self.dic.items():
            if scope=="":
                scope = "global"
            self.info["vars"].append((name, scope, type))
            self.info["tipos"].setdefault(type, []).append((name, scope))
            if not attr:
                self.info["erros"].append(f"[{scope}] [WARNING] Variable {name} declared but never used.") 
        self.info["vars"].sort(key=lambda x: (x[1],x[0]))
        return self.info
    
    def content(self,tree):
        self.visit_children(tree)

    def function(self,tree):
        self.scope = tree.children[1].value
        self.visit_children(tree)
        self.scope = ""

    def declaration(self,tree):
        name = tree.children[1].value
        key = (name,self.scope)
        type = self.visit(tree.children[0]).value
        if key not in self.dic:
            self.dic[key] = (type,[])
        else:
            scope = self.scope
            if self.scope == "":
                scope = "global"
            self.info["erros"].append(f"[ERROR] Variable {name} already declared in scope {scope}")

        if len(tree.children)>2:
            self.info["instrucao"]["attribution"] += 1
            #verificar se o tipo da expressão coincide com o tipo da variável
            self.dic[key][1].append(self.visit(tree.children[3]))

    
    def attribution(self,tree):
        name = self.visit(tree.children[0])
        key = (name,self.scope)
        
        self.info["instrucao"]["attribution"] += 1
        if key in self.dic:
            #verificar tipo da expressão depois
            self.dic[key][1].append(self.visit(tree.children[2]))

        else:
            # verificar se a varíavel está declarada no scope global
            if (name,"") in self.dic:
                key = (name,"")
                self.dic[key][1].append(self.visit(tree.children[2]))

            else:
                self.info["erros"].append(f"[ERROR] Variable {name} not declared")
    
    def body(self,tree):
        self.visit_children(tree)

    def variable(self,tree):
        return tree.children[0].value
    
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
        print(f"result len: {len(result)}")
        if len(result) == 1:
            if result[0].type == "INT":
                return int(result[0].value)
            elif result[0].type == "STRING":
                return result[0].value.strip('"')
            return result[0]
        else:
            return relationOperation(result[1], result[0], result[2])

    def factor_id(self,tree):
        id = self.visit_children(tree)[0].value
        # int b = a + 1 (variável não declarada)
        if (id, self.scope) not in self.dic:
            self.info["erros"].append(f"[ERROR] Variable {id} not declared.")
        # int a (declarada, mas não inicializada)
        # int b = a + 1
        elif not self.dic[(id,self.scope)][1]:
            self.info["erros"].append(f"[WARNING] Variable {id} not initialized.")

        
    def relational_op(self,tree):
        return tree.children[0].value
    
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
        return tree.children[0].value
    
    def mult_op(self,tree):
        return tree.children[0].value
    
    def factor(self,tree):
        result = self.visit_children(tree)
        if len(result) == 1:
            #tratar se for functionCall, problema no functionCall em si
            return result[0]
        else:
            return result[1](result[0])

    def uni_op(self,tree):
        return tree.children[0].value
    
    def function_call(self,tree):
        pass
        #self.scope = self.visit(tree.children[0])
        #self.visit(tree.children[1:])
        # no caso em que se atribui o valor de uma função a uma variável é preciso ver se os tipos batem certo

    def list_declaration(self,tree):
        #nao sei   def condition(self,tree):
        # é apenas um if, sem elif nem else
        if len(tree.children) == 3:
            self.if_condition += self.visit(tree.children[1])
            self.if_bodies.append(self.visit(tree.children[2]))
        # se tiver if e else
        elif len(tree.children) == 5:
            # se a condição do if for verdadeira
            if self.visit(tree.children[1]):
                self.visit(tree.children[2])
            else:
                self.visit(tree.children[4])
        # se tiver elif's e/ou else
        else:
            # se a condição do if for verdadeira
            if self.visit(tree.children[1]):
                self.visit(tree.children[2])
            # verificar se a condição dos elif's é verdadeira, se não, e existir else, executar o else
            else:
                for i, child in enumerate(tree.children[2:]):
                    if child.type == "ELIF" and self.visit(tree.children[i+1]):
                        self.visit(tree.children[i+2])
                        break
                    elif child.type == "ELSE":
                        self.visit(tree.children[i+1])
        pass
        # [12,3252+432,42354]
        # temos que mandar o tipo pa fora, yo
        pass

    def condition(self,tree):
        # é apenas um if, sem elif nem else
        if len(tree.children) == 3:
            if self.visit(tree.children[1]):
                self.visit(tree.children[2])
        # se tiver if e else
        elif len(tree.children) == 5:
            # se a condição do if for verdadeira
            if self.visit(tree.children[1]):
                self.visit(tree.children[2])
            else:
                self.visit(tree.children[4])
        # se tiver elif's e/ou else
        else:
            # se a condição do if for verdadeira
            if self.visit(tree.children[1]):
                self.visit(tree.children[2])
            # verificar se a condição dos elif's é verdadeira, se não, e existir else, executar o else
            else:
                for i, child in enumerate(tree.children[2:]):
                    if child.type == "ELIF" and self.visit(tree.children[i+1]):
                        self.visit(tree.children[i+2])
                        break
                    elif child.type == "ELSE":
                        self.visit(tree.children[i+1])

    def write(self,tree):
        self.info["instrucao"]["escrita"] += 1
        #isto seria se fosse para correr, não sei se é suposto
        #print(self.visit(tree.children[2]))

    def read(self,tree):
        self.info["instrucao"]["leitura"] += 1


    def cycle(self,tree):
        self.info["instrucao"]["cíclicas"] += 1
        self.visit(tree.children[1])
    
    def while_loop(self,tree):
        self.info["instrucao"]["cíclicas"] += 1
        self.visit(tree.children[2])
        
    def for_loop(self,tree):
        var_name = tree.children[1].value
        if (var_name,self.scope) in self.dic:
            self.info["erros"].append(f"[ERROR] Variable {var_name} already declared in scope {self.scope}")
        # ver o tipo do iteravel
        self.dict[(var_name,self.scope)] = ("?",[])
        self.info["instrucao"]["cíclicas"] += 1
        self.visit(tree.children[4])
        
        

    def iterable(self,tree):
        pass

    def add_elem(self,tree):
        pass
    
    # não funciona n sei pq
    def update_dic(self, key, child):
        if self.dic[key][0] == 'int':
            self.dic[key][1].append(int(self.visit(tree.children[child]).value))
        elif self.dic[key][0] == 'string':
            self.dic[key][1].append(self.visit(tree.children[child]).value.strip('"'))

frase = '''
int x = 1
void main():
    x = 2
    int y = 4
    while x < y:
        x = sum(1)
        y = y + 1

int sum(int n):
    int r = n + 1
    return r

list[int] nums = [1,2,3,4]
list[int] sums = [sum(1), sum(2)]

for n in nums:
    n = ((n*4)/2)^2
    do:
        n = n + x
    while (n % 2)

    if n % 2 == 0:
        nums[1:] = n
        print('numbers!')
        print(nums)
        int r = read(sys)

'''

frase1='''
x=3
int x=1
string z = "ola"
void main():
    int y = 4
    y = 2
    int x = 2
    z = "adeus"
''' 
'''
    while x < y:
        x = sum(1)
        y = y + 1'''
        
frase2 = '''
int x = 1 + 1
'''
        
ifs = '''
int x = 1
if x == 1:
    x = 3
'''

nao_funciona = '''
t = nums[1:3]
sys.out = sys.in //access error
'''

p = Lark(grammar, parser='lalr', postlex=TreeIndenter())
pydot__tree_to_png(p.parse(frase2), "tree.png")
tree = p.parse(frase2)  # retorna uma tree
data = DicInterpreter().visit(tree)
pprint.pprint(data)
