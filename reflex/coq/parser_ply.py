import ply.lex as lex
import sys

reserved = {
  'Components' : 'COMPONENTS',
  'Messages' : 'MESSAGES',
  'State' : 'STATE',
  'Init' : 'INIT',
  'Handlers' : 'HANDLERS',
  'Properties' : 'PROPERTIES',
  'When' : 'WHEN',
  'sends' : 'SENDS',
  'respond' : 'RESPOND',
  'nop' : 'NOP',
  'send' : 'SEND',
  'spawn' : 'SPAWN',
  'call' : 'CALL',
  'if' : 'IF',
  'then' : 'THEN',
  'else' : 'ELSE',
  'lookup' : 'LOOKUP',
  'forall' : 'FORALL',
  'ImmBefore' : 'IMMBEFORE',
  'ImmAfter' : 'IMMAFTER',
  'Enables' : 'ENABLES',
  'Ensures' : 'ENSURES',
  'Disables' : 'DISABLES',
  'NoInterfere' : 'NOINTERFERE',
  'Send' : 'KSEND',
  'Recv' : 'KRECV',
  'Spawn' : 'KSPAWN',
  'num' : 'TYPE_D',
  'str' : 'TYPE_D',
  'fd' : 'TYPE_D',
}

tokens = [
  'ID',
  'LPAREN',
  'RPAREN',
  'NUM',
  'STRING',
  'OP',
  'ASSIGN',
  'FUN',
  'WILDCARD',
  'COLON',
  'SEMICOLON',
  'COMMA',
  'LBRACE',
  'RBRACE',
  'LBRACKET',
  'RBRACKET',
] + list(reserved.values())

def t_ID(t):
  r'\w[\w\d]*'
  t.type = reserved.get(t.value,'ID')    # Check for reserved words
  return t

t_LPAREN = r'\('
t_RPAREN = r'\)'

def t_NUMBER(t):
  r'\d+'
  t.value = int(t.value)    
  return t

t_STRING = r'\".*?\"'
t_OP = r'\+|=='
t_ASSIGN = r'<-'
t_FUN = r'=>'
t_WILDCARD = r'_'
t_COLON = r':'
t_SEMICOLON = r';'
t_COMMA = r','
t_LBRACE = r'\['
t_RBRACE = r'\]'
t_LBRACKET = r'\{'
t_RBRACKET = r'\}'

# A string containing ignored characters (spaces and tabs)
t_ignore  = ' \t\n'

# Error handling rule
def t_error(t):
    print "Illegal character '%s'" % t.value[0]
    t.lexer.skip(1)

# Build the lexer
lexer = lex.lex()

spec = open(sys.argv[1]).read()

# Give the lexer some input
lexer.input(spec)

for tok in lexer:
  print tok

import ply.yacc as yacc

def p_prog(p):
  '''prog : COMPONENTS COLON comps \
            MESSAGES COLON msgs \
            STATE COLON state \
            INIT COLON init \
            HANDLERS COLON hdlrs \
            PROPERTIES COLON props
  '''
  p[0] = {'comps' : p[3], 'msgs' : p[6], 'state' : p[9],
          'init' : p[12], 'hdlrs' : p[15], 'props' : p[18]}

def p_comps(p):
  '''comps : comp comps
           | comp
  '''
  if len(p) == 3:
    p[0] = [p[1]] + p[2]
  else:
    p[0] = [p[1]]

def p_comp(p):
  'comp : ID STRING LPAREN stringlist RPAREN LPAREN typelist RPAREN'
  p[0] = {'tag' : p[1], 'cmd' : p[2], 'args' : p[4], 'types' : p[7]}

def p_msgs(p):
  '''msgs : msg msgs
          | msg
  '''
  if len(p) == 3:
    p[0] = [p[1]] + p[2]
  else:
    p[0] = [p[1]]

def p_msg(p):
  'msg : ID LPAREN typelist RPAREN'
  p[0] = {'tag' : p[1], 'types' : p[3]}

def p_state(p):
  '''state : stvar state
           | stvar
           |
  '''
  if len(p) == 3:
    p[0] = [p[1]] + p[2]
  elif len(p) == 2:
    p[0] = [p[1]]
  else:
    p[0] = []

def p_stvar(p):
  '''stvar : ID COLON TYPE_D
           | ID COLON ID
  '''
  p[0] = {'var' : p[1], 'type' : p[3]}

def p_init(p):
  'init : cmd'
  p[0] = p[1]

def p_hdlrs(p):
  '''hdlrs : hdlr hdlrs
           | hdlr
  '''
  if len(p) == 3:
    p[0] = [p[1]] + p[2]
  else:
    p[0] = [p[1]]

def p_props(p):
  '''props : traceprop props
           | niprop props
           | traceprop
           | niprop
  '''
  if len(p) == 3:
    p[0] = [p[1]] + p[2]
  else:
    p[0] = [p[1]]

def p_hdlr(p):
  '''hdlr : WHEN ID LPAREN idlist RPAREN \
            SENDS ID LPAREN idlist RPAREN \
            RESPOND COLON cmd
  '''
  p[0] = {'ctag' : p[2], 'cfg' : p[4], 'mtag' : p[7],
          'pl' : p[9], 'cmd'  : p[13]}

def p_cmd(p):
  '''cmd : NOP
         | assign
         | seq
         | send
         | spawn
         | call
         | ite
         | lookup
  '''
  p[0] = p[1]

def p_assign(p):
  'assign : ID ASSIGN expr'
  p[0] = {'type' : 'assign', 'var' : p[1], 'expr' : p[3]}

def p_seq(p):
  'seq : cmd SEMICOLON cmd'
  p[0] = {'type' : 'seq', 'cmd1' : p[1], 'cmd2' : p[3]}

def p_send(p):
  'send : SEND LPAREN expr COMMA ID LPAREN exprlist RPAREN RPAREN'
  p[0] = {'type' : 'send', 'expr' : p[3], 'mtag' : p[5], 'pl' : p[7]}

def p_spawn(p):
  'spawn : ID ASSIGN SPAWN ID LPAREN exprlist RPAREN'
  p[0] = {'type' : 'spawn', 'var' : p[1], 'ctag' : p[4], 'cfg' : p[6]}

def p_call(p):
  'call : ID ASSIGN CALL expr LPAREN exprlist RPAREN'
  p[0] = {'type' : 'call', 'var' : p[1], 'cmd' : p[4], 'args' : p[6]}

def p_ite(p):
  'ite : IF expr THEN cmd ELSE cmd'
  p[0] = {'type' : 'ite', 'cond' : p[2], 'cmd1' : p[4], 'cmd2' : p[6]}

def p_lookup(p):
  '''lookup : LOOKUP ID LPAREN patexprlist RPAREN \
              LBRACKET ID FUN cmd RBRACKET \
              LBRACKET cmd RBRACKET
  '''
  p[0] = {'type' : 'lookup', 'ctag' : p[2],
          'cfg' : p[4], 'var' : p[7],
          'cmd1' : p[9], 'cmd2' : p[12]}

def p_traceprop(p):
  'traceprop : FORALL idlist COLON tprop'
  p[0] = {'ids' : p[2], 'tprop' : p[4]}

def p_tprop(p):
  '''tprop : LBRACE apat RBRACE IMMBEFORE LBRACE apat RBRACE
           | LBRACE apat RBRACE IMMAFTER LBRACE apat RBRACE
           | LBRACE apat RBRACE ENABLES LBRACE apat RBRACE
           | LBRACE apat RBRACE ENSURES LBRACE apat RBRACE
           | LBRACE apat RBRACE DISABLES LBRACE apat RBRACE
  '''
  p[0] = {'type' : p[4], 'pat1' : p[2], 'pat2' : p[6]}

def p_niprop(p):
  'niprop : NOINTERFERE cpatlist idlist'
  p[0] = {'cpats' : p[2], 'ids' : p[3]}

def p_apat(p):
  '''apat : KSEND LPAREN ID COMMA ID LPAREN patlist RPAREN RPAREN
          | KRECV LPAREN ID COMMA ID LPAREN patlist RPAREN RPAREN
          | KSPAWN ID LPAREN patlist RPAREN
  '''
  p[0] = {'type' : p[1]}
  if p[0]['type'] == 'Send' or p[0]['type'] == 'Recv':
    p[0]['ctag'] = p[3]
    p[0]['mtag'] = p[5]
    p[0]['mpat'] = p[7]
  elif p[0]['type'] == 'Spawn':
    p[0]['ctag'] = p[2]
    p[0]['cpat'] = p[4]

def p_patexprlist(p):
  '''patexprlist : expr COMMA patexprlist
                 | pat COMMA patexprlist
                 | expr
                 | pat
                 |
  '''
  if len(p) == 4:
    p[0] = [p[1]] + p[3]
  elif len(p) == 2:
    p[0] = [p[1]]
  else:
    p[0] = []

def p_exprlist(p):
  '''exprlist : expr COMMA exprlist
              | expr
              |
  '''
  if len(p) == 4:
    p[0] = [p[1]] + p[3]
  elif len(p) == 2:
    p[0] = [p[1]]
  else:
    p[0] = []

def p_expr(p):
  '''expr : expr OP expr
          | OP expr
          | idexpr
          | numexpr
          | stringexpr
  '''
  p[0] = {}
  if len(p) == 4:
    p[0]['type'] = 'binop'
    p[0]['expr1'] = p[1]
    p[0]['expr2'] = p[3]
  elif len(p) == 3:
    p[0]['type'] = 'unop'
    p[0]['expr'] = p[2]
  else:
    p[0] = p[1]

def p_idexpr(p):
  'idexpr : ID'
  p[0] = {'type' : 'id', 'val' : p[1]}

def p_numexpr(p):
  'numexpr : NUM'
  p[0] = {'type' : 'num', 'val' : p[1]}

def p_stringexpr(p):
  'stringexpr : STRING'
  p[0] = {'type' : 'string', 'val' : p[1]}

def p_cpatlist(p):
  '''cpatlist : cpat COMMA cpatlist
              | cpat
              |
  '''
  if len(p) == 4:
    p[0] = [p[1]] + p[3]
  elif len(p) == 2:
    p[0] = [p[1]]
  else:
    p[0] = []

def p_cpat(p):
  'cpat : ID LPAREN patlist RPAREN'
  p[0] = {'id' : p[1], 'pats' : p[3]}

def p_patlist(p):
  '''patlist : pat COMMA patlist
             | pat
             |
  '''
  if len(p) == 4:
    p[0] = [p[1]] + p[3]
  elif len(p) == 2:
    p[0] = [p[1]]
  else:
    p[0] = []

def p_pat(p):
  '''pat : WILDCARD
         | NUM
         | STRING
         | ID
  '''
  p[0] = p[1]

def p_idlist(p):
  '''idlist : ID COMMA idlist
            | ID
            |
  '''
  if len(p) == 4:
    p[0] = [p[1]] + p[3]
  elif len(p) == 2:
    p[0] = [p[1]]
  else:
    p[0] = []

def p_stringlist(p):
  '''stringlist : STRING COMMA stringlist
                | STRING
                |
  '''
  if len(p) == 4:
    p[0] = [p[1]] + p[3]
  elif len(p) == 2:
    p[0] = [p[1]]
  else:
    p[0] = []

def p_typelist(p):
  '''typelist : TYPE_D COMMA typelist
              | TYPE_D
              |
  '''
  if len(p) == 4:
    p[0] = [p[1]] + p[3]
  elif len(p) == 2:
    p[0] = [p[1]]
  else:
    p[0] = []

# Error rule for syntax errors
def p_error(p):
  print p
  print "Syntax error in input!"

# Build the parser
parser = yacc.yacc()

result = parser.parse(spec)
print result

out = open(sys.argv[2], 'w')

def write_prelude():
  out.write("Require Import String.\n")
  out.write("Require Import Reflex.\n")
  out.write("Require Import ReflexBase.\n")
  out.write("Require Import ReflexDenoted.\n")
  out.write("Require Import ReflexFin.\n")
  out.write("Require Import ReflexFrontend.\n")
  out.write("Require Import ReflexHVec.\n")
  out.write("Require Import ReflexIO.\n")
  out.write("Require Import ReflexVec.\n")
  out.write("Require Import Misc.\n")
  out.write("Require Import Ascii.\n\n")
  out.write("Open Scope string_scope.\n\n")
  out.write("Module SystemFeatures <: SystemFeaturesInterface.\n\n")

spec_to_desc = { 'str' : 'str_d', 'fd' : 'fd_d', 'num' : 'num_d' }

def get_desc(x):
  return spec_to_desc[x]

def get_cdesc(x):
  if x in spec_to_desc:
    return 'Desc _ ' + spec_to_desc[x]
  else:
    return 'Comp _ ' + x

def arg_types_str(args):
  return "[" + "; ".join(map(get_desc, args)) + "]"

def gen_fin_notation(l):
  fin = 0
  for e in l:
    out.write("Notation " + e + " := " + str(fin) + "%fin (only parsing).\n")
    fin += 1

def process_comps(comps):
  out.write("Inductive COMPT' : Type :=\n")
  for c in comps:
    out.write("| " + c['tag'] + "\n")
  out.write(".\n\n")
  out.write("Definition COMPT := COMPT'.\n\n")
  out.write("Definition COMPTDEC : forall (x y : COMPT), decide (x = y).\n")
  out.write("Proof. decide equality. Defined.\n\n")
  out.write("Definition COMPS (t : COMPT) : compd :=\n")
  out.write("  match t with\n")
  for c in comps:
    out.write("  | " + c['tag'] + "=> mk_compd\n")
    out.write("    \"" + c['tag'] + "\" " + c['cmd'] + " [" + "; ".join(c['args']) + "]\n")
    out.write("    (mk_vdesc " + arg_types_str(c['types']) + ")\n")
  out.write("end.\n\n")

def process_msgs(msgs):
  out.write("Definition NB_MSG : nat := " + str(len(msgs)) + ".\n\n")
  out.write("Definition PAYD := mk_vvdesc\n")
  out.write("[\n")
  out.write(";\n".join(map(lambda m: "(\"" + m['tag'] + "\"," + arg_types_str(m['types']) + ")", msgs)))
  out.write("\n].\n\n")
  gen_fin_notation(map(lambda m: m['tag'], msgs))
  out.write("\n")

def get_envd_seq(cmd, cont):
  return dict(cont(cmd['cmd1']), **cont(cmd['cmd2']))

def get_envd_spawn(cmd, cont):
  return {cmd['var'] : 'Comp _ ' + cmd['ctag']}

def get_envd_call(cmd, cont):
  return {cmd['var'] : 'Desc _ fd_d'}

def get_envd_ite(cmd, cont):
  return dict(get_envd(cmd['cmd1']), **get_envd(cmd['cmd2']))

def get_envd_lookup(cmd, cont):
  return dict(dict({cmd['var'] : cmd['ctag']},
    **get_envd(cmd['cmd1'])), **get_envd(cmd['cmd2']))

def get_envd(cmd):
  return {
     'assign' : lambda x ,y: {},
     'seq'    : get_envd_seq,
     'send'   : lambda x, y: {},
     'spawn'  : get_envd_spawn,
     'call'   : get_envd_call,
     'ite'    : get_envd_ite,
     'lookup' : get_envd_lookup
    }[cmd['type']](cmd, get_envd)

def process_init_envd(init):
  out.write("Definition IENVD : vcdesc COMPT := mk_vcdesc\n")
  out.write("  [\n")
  envd = get_envd(init).items()
  out.write("   " + ";\n   ".join(map(lambda x: x[1], envd)))
  out.write("\n  ].\n\n")
  gen_fin_notation(map(lambda x: x[0], envd))
  out.write("\n")

def process_kstd(state):
  out.write("Definition KSTD : vcdesc COMPT := mk_vcdesc\n")
  out.write("  [\n")
  out.write("   " + ";\n   ".join(map(lambda s: get_cdesc(s['type']), state)))
  out.write("\n  ].\n\n")
  gen_fin_notation(map(lambda s: s['var'], state))
  out.write("\n")

def end_sys_features():
  out.write("End SystemFeatures.\n\n")
  out.write("Import SystemFeatures.\n\n")
  out.write("Module Language := MkLanguage(SystemFeatures).\n\n")
  out.write("Import Language.\n\n")
  out.write("Module Spec <: SpecInterface.\n\n")
  out.write("Include SystemFeatures.\n\n")

def get_expr(expr):
  if expr['type'] == 'binop':
    pass
  elif expr['type'] == 'unop':
    pass
  elif expr['type'] == 'id':
    pass
  elif expr['type'] == 'num':
    pass
  elif expr['type'] == 'string':
    pass

def get_init_assign(cmd, cont):
  return 'stupd _ IENVD ' + cmd['var'] + '(' + get_expr(cmd['expr']) + ')'

def get_init_seq(cmd, cont):
  return '  seq (' + cont(cmd['cmd1']) + ') (\n' + cont(cmd['cmds']) + ')'

def get_init_send(cmd, cont):
  pass

def get_init_spawn(cmd, cont):
  pass

def get_init_call(cmd, cont):
  pass

def get_init_ite(cmd, cont):
  pass

def get_init_lookup(cmd, cont):
  pass

def get_init_cmd(cmd):
  return {
    'assign' : get_init_assign,
    'seq'    : get_init_seq,
    'send'   : get_init_send,
    'spawn'  : get_init_spawn,
    'call'   : get_init_call,
    'ite'    : get_init_ite,
    'lookup' : get_init_lookup
  }[cmd['type']](cmd, get_init_cmd)

def process_init(init):
  out.write("Definition INIT : init_prog PAYD COMPT COMPS KSTD IENVD :=\n")
  out.write(get_init_cmd(init))

write_prelude()
process_msgs(result['msgs'])
process_comps(result['comps'])
process_init_envd(result['init'])
process_kstd(result['state'])
end_sys_features()
