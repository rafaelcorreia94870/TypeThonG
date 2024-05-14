import lark.tree as lark_tree
import lark.lexer as lark_lexer

from lark import Lark
from lark.indenter import Indenter
from lark.tree import pydot__tree_to_png
from lark.visitors import Interpreter

import os
import pprint
import graphviz
from collections import Counter
from jinja2 import Environment, FileSystemLoader
#dicionario com as chaves como variavel, scope e o seu valor os valores que lhe foram atribuidos

grammar = r'''
    // Regras Sintaticas - typethong script.tt
    start: _NL* content*

    content: declaration (_NL)*
           | attribution (_NL)*
           | cycle (_NL)*
           | write (_NL)*
           | read (_NL)*
           | condition
           | add_elem
           | RETURN expression (_NL)* -> return
           | expression
           | function

    function: (type|T_VOID) ID LCP ( | type ID (COMMA type ID)* ) RCP body

    declaration: type ID (EQUALS expression)?

    attribution: variable EQUALS expression
    
    body: ":" _NL+ _INDENT content+ _DEDENT

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
           | variable                 -> factor_id
           | list_declaration
           
    uni_op : PLUS | MINUS | NOT
     
    condition: IF expression body (ELIF expression body)* (ELSE body)?
             | MATCH variable COLON _NL _INDENT (WITH expression body)+ _DEDENT

    write: PRINT LCP expression RCP

    read: READ LCP RCP
    
    function_call : ID LCP ( | expression (COMMA expression)*) RCP
    list_declaration : LSP (expression (COMMA expression)*)? RSP

    cycle: DO body WHILE expression -> do_while_loop
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
        self._scope = self.scope if self.scope != '' else 'global'
        self.nested = False
        self.nested_acc = []
        self.last_visited = []
        self.first_last = False
    
    # vars= [(ID,scope,type),...] 
    # errors = [lista de erros]
    # types[Tipo de dados] = [(id,scope),..]
    # instructions = {total: int, atribuicoes: int, leitura: int, escrita, int, condicionais: int, cíclicas : int}
    # mausif : in
    # listaif = [strings,..] 
    # cfg = {global: string, funcao1: string, ...}
    def start(self,tree):
        self.info = {"vars": [], "errors": [], "types": Counter(), "instructions": Counter(), "nifs": 0, "nested_ifs": [], "cfg": {}}
        self.info['cfg']['global'] = '''digraph global{
    beautify = true;
    graph [fontname = "JetBrains Mono", color=\"#93d38a\", pad=\"0.5\"];
    node [fontname = "JetBrains Mono", color=\"#93d38a\", fontcolor=\"#ffffff\", style="filled", fillcolor=\"#0e330a\"];
    edge [fontname = "JetBrains Mono", color=\"#ea3cbe\"];
    bgcolor=\"#0d1117\";
    inicio [fontcolor="#88f17e"];\n\n'''
         
        #self.info['cfg']['global'] = "digraph global{\nbgcolor=\"#0d1117\";\n"
        self.visit_children(tree)
        for (name, scope), (type, attr) in self.dic.items():
            if scope=="":
                scope = "global"
            self.info["vars"].append((name, scope, type))
            self.info["types"][type]+=1
            if not attr:
                self.info["errors"].append(f"[{scope}] [WARNING] Variable {name} declared but never used.") 
        self.info["vars"].sort(key=lambda x: (x[1],x[0]))
        self.info["types"] = self.info["types"].items()
        
        self.create_cfg()
        
        return self.info
    
    def content(self,tree):
        if self.nested and len(tree.children) == 1 and tree.children[0].data == 'condition':
            self.nested = True
        else:
            if len(self.nested_acc) > 1:
                finalResult = " and ".join(self.nested_acc)+":"
                before = self.nested_acc[0] + ": \n" + "".join(["if " + i + ": \n " for i in self.nested_acc[1:]])
                self.info['nested_ifs'].append(before+" => "+finalResult)
            self.nested_acc = []
            self.nested = False

        expr = self.visit_children(tree)[0]
        return expr

    def function(self,tree):
        self.scope = tree.children[1].value
        self.visit_children(tree)
        self.scope = ""

    def declaration(self,tree):
        name = tree.children[1].value
        key = (name,self.scope)
        type = self.visit(tree.children[0])
        value = ''
        
        if key not in self.dic:
            self.dic[key] = (type,[])
        else:
            scope = self.scope
            if self.scope == "":
                scope = "global"
            self.info["errors"].append(f"[ERROR] Variable {name} already declared in scope {scope}")

        if len(tree.children)>2:
            self.info["instructions"]["attribution"] += 1
            #verificar se o tipo da expressão coincide com o tipo da variável
            self.dic[key][1].append(self.visit(tree.children[3]))
            value = str(self.visit(tree.children[3]))
        
            expr = f"{type} {name} = {value}"        
            self.add_to_graph([expr])
            return [expr]
        else:
            expr = f"{type} {name}"
            self.add_to_graph([expr])
            return [expr]
        
    def attribution(self,tree):
        name = self.visit(tree.children[0])
        key = (name,self.scope)
        value = str(self.visit(tree.children[2]))
       
        if key in self.dic:
            #verificar tipo da expressão depois
            self.dic[key][1].append(self.visit(tree.children[2]))
            self.info["instructions"]["attribution"] += 1

        else:
            # verificar se a varíavel está declarada no scope global
            if (name,"") in self.dic:
                key = (name,"")
                self.dic[key][1].append(self.visit(tree.children[2]))
                self.info["instructions"]["attribution"] += 1

            else:
                self.info["errors"].append(f"[ERROR] Variable {name} not declared")
                
        expr = f"{name} = {value}"
        self.add_to_graph([expr])
        return [expr]
    
    def body(self,tree):
        children_expr = self.visit_children(tree)

        # devolver o último elemento para fazer a ligaçao ao próximo nodo no CFG
        return children_expr[0], children_expr[-1]

    def variable(self,tree):
        return tree.children[0].value
    
    #def access(self,tree):
    #    return self.visit(tree.children[0])

    def type(self,tree):
        result = self.visit_children(tree)
        if len(result) == 1:
            return str(result[0])
        else:
            return "".join(result)
        
    def expression(self,tree):
        result = self.visit_children(tree)
       # print(f"result: {result}")
        if len(result) == 1:
            #check if result[0] is a list
            if result[0].__class__.__name__ == "str":
                return result[0]
            elif result[0].__class__.__name__ == "list":
                return result[0]
            elif result[0].type == "INT":
                return int(result[0].value)
            elif result[0].type == "STRING":
                return result[0].value.strip('"')
            return result[0]
        else:
            return " ".join([str(result[0]),str(result[1]),str(result[2])])#relationOperation(result[1], result[0], result[2])

    def factor_id(self,tree):
        id = self.visit_children(tree)[0]
        # int b = a + 1 (variável não declarada)
        if (id, self.scope) not in self.dic:
            self.info["errors"].append(f"[ERROR] Variable {id} not declared.")
        # int a (declarada, mas não inicializada)
        # int b = a + 1
        elif not self.dic[(id,self.scope)][1]:
            self.info["errors"].append(f"[WARNING] Variable {id} not initialized.")
        return id
   
    def relational_op(self,tree):
        return tree.children[0].value
    
    def priority_expr(self,tree):
        result = self.visit_children(tree)
        if len(result) == 1:
            return result[0]
        else:
            return " ".join([str(result[0]),str(result[1]),str(result[2])]) #addOperation(result[1], result[0], result[2])

    def term(self,tree):
        result = self.visit_children(tree)
        if len(result) == 1:
            return result[0]
        else:
            return " ".join([str(result[0]),str(result[1]),str(result[2])]) #multOperation(result[1], result[0], result[2])

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
            return result[1]

    def uni_op(self,tree):
        return tree.children[0].value
    
    def function_call(self,tree):
        function_name = tree.children[0].value
        arguments = self.visit_children(tree)[2:-1]
        # fazer a funcao str a todos os argumentos
        arguments = [str(arg) for arg in arguments]
        return function_name+"("+"".join(arguments)+")"
        #self.scope = self.visit(tree.children[0])
        #self.visit(tree.children[1:])
        # no caso em que se atribui o valor de uma função a uma variável é preciso ver se os tipos batem certo

    def list_declaration(self,tree):
        list_d = "".join([str(elem) for elem in self.visit_children(tree)])
        return list_d

    def condition(self,tree):
        # é apenas um if, sem elif nem else
        self.info["instructions"]["condicionais"] += 1
        
        if len(tree.children) == 3:
            if_expr = self.visit(tree.children[1])
            if self.nested_acc: # se houver nested ifs
                self.info['nifs'] += 1
                self.nested_acc.append(if_expr)
            else:
                self.nested_acc.append("if " + if_expr)
            self.nested = True
            
            self.add_to_graph(["if " + if_expr])
            _, if_last = self.visit(tree.children[2])
            
            #print(if_last)
            
            expr = ["if " + if_expr] + if_last

            #print(expr)

            self.last_visited = expr
            
        # se tiver if e else
        elif len(tree.children) == 5:
            if_expr = self.visit(tree.children[1])
            expressao = "if " + if_expr
            self.add_to_graph([expressao])
            if self.nested == False:
            # if 
                self.nested_acc.append(expressao)
                self.nested = True
                # cfg
                _, if_last = self.visit(tree.children[2])
                self.last_visited = [expressao]
                
            # else
                self.nested_acc = []
                self.nested = False
                # cfg
                _, else_last = self.visit(tree.children[4])
                expr = if_last + else_last
                self.last_visited = expr
                
            else:
                _, if_last = self.visit(tree.children[2])
                self.last_visited = [expressao]
                
                _, else_last = self.visit(tree.children[4])
                expr = if_last + else_last
                self.last_visited = expr

        # se tiver elif's e/ou else
        else:
            # visitar if
            if self.nested_acc: # se houver nested ifs
                self.nested_acc= ["if "+self.visit(tree.children[1])]
            else:
                self.nested_acc.append("if "+self.visit(tree.children[1]))
            self.nested = True
        
            self.visit(tree.children[2])
            
            # visitar elif's, e se existir else
            for i, child in enumerate(tree.children):
                if isinstance(child,lark_lexer.Token) and child.type == "ELIF":
                    self.info["instructions"]["condicionais"] += 1
                    self.nested_acc.append("elif "+self.visit(tree.children[i+1]))
                    self.nested = True
                    self.visit(tree.children[i+2])

                elif isinstance(child,lark_lexer.Token) and child.type == "ELSE":
                    self.nested_acc = []
                    self.nested = False
                    self.visit(tree.children[i+1])
        
        return expr

    def write(self,tree):
        self.info["instructions"]["escrita"] += 1
        #isto seria se fosse para correr, não sei se é suposto
        expr = f"print({self.visit(tree.children[2])})"
        self.add_to_graph([expr])
        return [expr]

    def read(self,tree):
        self.info["instructions"]["leitura"] += 1
        expr = "read()"
        self.add_to_graph([expr])
        return [expr]

    def cycle(self,tree):
        self.info["instructions"]["cíclicas"] += 1
        self.visit(tree.children[1])
    
    def while_loop(self,tree):
        self.info["instructions"]["cíclicas"] += 1
        # cfg
        expr = f"while {self.visit(tree.children[1])}"
        
        self.add_to_graph([expr])
        _, last_while = self.visit(tree.children[2])
        self.add_to_graph_single(last_while, [expr])
        self.last_visited = [expr]
        
        return [expr]
    
    def do_while_loop(self,tree):
        self.info["instructions"]["cíclicas"] += 1
        
        # cfg
        first_do, last_do = self.visit(tree.children[1])
        expr = f"while {self.visit(tree.children[3])}"
        # jabardo para garantir que só volta ao primeiro
        first_do = [first_do[0]]
        self.add_to_graph_single(last_do, [expr])
        self.add_to_graph_single([expr], first_do)
        
        return [expr]
        
    def for_loop(self,tree):
        var_name = tree.children[1].value
        typeVar,values,var_iter = self.visit(tree.children[3])
        if (var_name,self.scope) in self.dic:
            scope = "global" if self.scope == "" else self.scope    
            self.info["errors"].append(f"[ERROR] Variable {var_name} already declared in scope {scope}")
        else:
            self.dic[(var_name,self.scope)] = (typeVar,values)
        self.info["instructions"]["cíclicas"] += 1
        
        # cfg
        
        expr = f"for {var_name} in {var_iter}"
        
        self.add_to_graph([expr])
        _, last_for = self.visit(tree.children[4])
        self.add_to_graph_single(last_for, [expr])
        self.last_visited = [expr]   
        
        return [expr]
        
    def iterable(self,tree):
        if len(tree.children)==1:
            variable = self.visit(tree.children[0])
            if (variable, self.scope) not in self.dic:
                self.info["errors"].append(f"[ERROR] Variable {variable} not declared.")
                return None,[],variable
            elif not self.dic[(variable,self.scope)][1]:
                self.info["errors"].append(f"[WARNING] Variable {variable} not initialized.")
                typeList = self.dic[(variable,self.scope)][0]
                return typeList.split("[")[1].split("]")[0],["error"],variable
            else:
                typeList = self.dic[(variable,self.scope)][0]
                return (typeList.split("[")[1].split("]")[0], self.dic[(variable,self.scope)][1]),variable
                
        else:
            return "int"

    def add_elem(self,tree):
        pass

    def add_to_graph(self, expr):
        condition = ['if', 'for', 'while']
        
        if self.last_visited == []:
            for expression in expr:
                self.create_edge("inicio", expression)
                # criar nodo diamond para condições
                if expression.split()[0] in condition:
                    self.create_edge(expression, styles={"shape": "diamond", 
                                                         "style": "filled", 
                                                         "fillcolor": "#4a1241"})
        else:
            for last in self.last_visited:
                for expression in expr:
                    self.create_edge(last, expression)
                    # criar nodo diamond para condições
                    if expression.split()[0] in condition:
                        self.create_edge(expression, styles={"shape": "diamond", 
                                                             "style": "filled", 
                                                             "fillcolor": "#4a1241"})
        
        self.last_visited = expr
        
    def add_to_graph_single(self, org, dest):
        condition = ['if', 'for', 'while']
        for o in org:
            for d in dest:
                self.create_edge(o, d)
                # criar nodo diamond para condições
                if o.split()[0] in condition:
                    self.create_edge(o, styles={"shape": "diamond", 
                                                "style": "filled", 
                                                "fillcolor": "#4a1241"})

        self.last_visited = dest

    def create_edge(self, org, dest=None, styles={}):
        # styles = {style: "filled", fillcolor: "#4a1241"}
        # styles_string = "[style=filled, fillcolor=\"#4a1241\"]"
        if styles:
            styles_string = f"[" + ", ".join([f"{k}=\"{v}\"" for k, v in styles.items()]) + "];"
            if dest != None:
                self.info['cfg'][self._scope] += f'    "{org}" -> "{dest}" {styles_string}\n'
            else:
                self.info['cfg'][self._scope] += f'    "{org}" {styles_string}\n'
        else:
            self.info['cfg'][self._scope] += f'    "{org}" -> "{dest}"\n'
                    
    def create_cfg(self):
        # for each scope build a CFG graph (in DOT format)
        """
        Code example:
        int x
        int y = 1
        y = 2
        if x:
            print(x)
        read()
        
        Graph example:
        digraph G {
            inicio -> "int x"
            "int x" -> "int y = 1"
            "int y = 1" -> "y = 2"
            "y = 2" -> "if x"
            "if x" -> "print x"
            "if x" -> ""
            "print(x)" -> ""
            "" -> "read()"
            "read()" -> fim
        }
        """
        
        # para terminar o grafo
        for last in self.last_visited:
            self.create_edge(last, "fim")
        self.create_edge("fim", styles={"shape": "doublecircle", "fontcolor": "#ff3024"})
        self.info['cfg'][self._scope] += "}\n"
        
        for scope, graph in self.info['cfg'].items():
            print(graph)
            # Create a Graph object from the DOT graph
            dot_graph = graphviz.Source(graph)

            # create cfg folder inside outputs if it doesn't exist
            if not os.path.exists("outputs/cfg"):
                os.makedirs("outputs/cfg")

            # Save the graph as an image file (PNG format in this case) in outputs folder
            dot_graph.render(f"{self._scope}",
                             directory="outputs/cfg",
                             format="png",
                             cleanup=True)

frase = '''
list[int] nums = [1,2,3,4]
for n in nums:
    n = ((n*4)/2)^2
    do:
        n = n + x
    while (n % 2)
int x = 1
int a = 2

if x:
    read()
    print("1234")
elif a:
    if b:
        x = 2    
        
if x:
    if y:
        if z:
            x = 1 + 1
            list[int] nums = [1,2,3,4]
elif a:
    if z:
        int c
    elif x:
        if y:
            int d
        
elif e:
    if d:
        int f
    else:
        int g
        
else:
    int h
    
if x:
    if y:
        int z
    elif w:
        if a:
            int v
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
    x = x + 1
    while x<y :
        x = add(1,4)
        y = y + 1

'''
        
frase2 = '''
int x = 1 + 1
list[int] nums = [1,2,3,4]
nums[1]=3
nums.out = nums[1]
'''

ex1 = """
int main():
    int x 
    int y = 1
    return y
"""

ex2 = """
list[int] cenas = [1,2,3,4]
int z = 3
string z = 4 
for z in cenas: 
    print(z)
"""

ex3 = """
int x = y + 1 
z = x + 1
"""

ex4 ="""
int x 
int y = x + 1
list[int] cenas
for n in cenas:
    x = n + 1
"""

ex5 = '''
int x
int y
int z
int a
if x:
    if y:
        if z:
            x = 1 + 1
            list[int] nums = [1,2,3,4]
elif a:
    if z:
        int c
    elif x:
        if y:
            int d
        
elif e:
    if d:
        int f
    else:
        int g
        
else:
    int h
    
if x:
    if y:
        int z
    elif w:
        if a:
            int v
'''

teste = """
if x:
    if y:
        if z:
            x = 1 + 1
            list[int] nums = [1,2,3,4]
elif a:
    if z:
        int c
        
elif e:
    if d:
        int f
    else:
        int g
        
else:
    int h
"""

cfg_if = """
int x
if x:
    print(x)
    if y:
        int z
        read()
"""

cfg_ifelse = """
if x:
    if a:
        int a = 1
    else:
        int x = 3
else:
    int b = 2
read()
"""

cfg_forwhile = """
for x in xs:
    int x = 1
    while w < 10:
        int w = 2
        int z = 3
while z < 10:
    int v = 2
    for y in ys:
        int y = 2
        int w = 3
"""

cfg_dowhile = """
int x = 1
do:
    for y in ys:
        int y = 2
    while y < 10:
        y = y + 1
while x < 10
"""

# ainda tem erros estupidos
cfg_completo = """
if x:
    while x < 10:
        if y:
            for x in xs:
                read()
                print('res')
        else:
            do:
                if x < y:
                    print(x)
            while y < 10
print('Thats all folks!')
"""

def generate_html(frase):
    print(frase)
    code_ex = frase.strip()

    p = Lark(grammar, parser='lalr', postlex=TreeIndenter())
    tree = p.parse(code_ex)  # retorna uma tree
    variables = DicInterpreter().visit(tree)
    pprint.pprint(variables)
    pydot__tree_to_png(tree, "outputs/trees/tree.png")


    env = Environment(loader=FileSystemLoader('.'))

    # Load your HTML template
    template = env.get_template('templates/ttg-template.html')

    variables["code"] = code_ex
    # Render the template with variables
    output = template.render(variables)
    with open("templates/typethong-info.html", "w") as f:
        f.write(output)
        
def main():

    code_ex = cfg_dowhile

    p = Lark(grammar, parser='lalr', postlex=TreeIndenter())
    tree = p.parse(code_ex)  # retorna uma tree
    variables = DicInterpreter().visit(tree)
    #pprint.pprint(variables)
    
    # create trees folder inside outputs if it doesn't exist
    if not os.path.exists("outputs/trees"):
        os.makedirs("outputs/trees")
    pydot__tree_to_png(tree, "outputs/trees/tree.png")

    env = Environment(loader=FileSystemLoader('.'))

    # Load your HTML template
    template = env.get_template('templates/ttg-template.html')

    variables["code"] = code_ex
    # Render the template with variables
    output = template.render(variables)

    with open("outputs/typethong-info.html", "w") as f:
        f.write(output)
    
if __name__ == '__main__':
    main()
    
    
# mail: aaragao@di.uminho.pt -> António Aragão
# Conta na máquina EPL para publicação

