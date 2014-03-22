import ply.lex as lex
import ply.yacc as yacc
import sys
import re
from sets import Set
import logging

logging.basicConfig(
    level = logging.DEBUG,
    filename = "parselog.txt",
    filemode = "w",
    format = "%(filename)10s:%(lineno)4d:%(message)s"
)
log = logging.getLogger()

reserved = {
  'Components' : 'COMPONENTS',
  'Messages' : 'MESSAGES',
  'State' : 'STATE',
  'Operations' : 'OPERATIONS',
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
  'invokefd' : 'INVOKEFD',
  'invokestr' : 'INVOKESTR',
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
  'HighComps' : 'HIGHCOMPS',
  'HighVars' : 'HIGHVARS',
  'HighCompList' : 'HIGHCOMPLIST',
  'Send' : 'KSEND',
  'Recv' : 'KRECV',
  'Spawn' : 'KSPAWN',
  'Call' : 'KCALL',
  'InvokeFD' : 'KINVOKEFD',
  'InvokeStr' : 'KINVOKESTR',
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
  'RARROW',
  'WILDCARD',
  'COLON',
  'SEMICOLON',
  'COMMA',
  'LBRACE',
  'RBRACE',
  'LBRACKET',
  'RBRACKET',
  'DOT',
] + list(reserved.values())

def t_ID(t):
  r'[a-zA-Z][\w]*'
  t.type = reserved.get(t.value,'ID')    # Check for reserved words
  return t

t_LPAREN = r'\('
t_RPAREN = r'\)'

def t_NUM(t):
  r'\d+'
  t.value = int(t.value)    
  return t

t_STRING = r'\".*?\"'
t_OP = r'\+\+|\+|=='
t_ASSIGN = r'<-'
t_FUN = r'=>'
t_RARROW = r'->'
t_WILDCARD = r'_'
t_COLON = r':'
t_SEMICOLON = r';'
t_COMMA = r','
t_LBRACE = r'\['
t_RBRACE = r'\]'
t_LBRACKET = r'\{'
t_RBRACKET = r'\}'
t_DOT = r'\.'

# A string containing ignored characters (spaces and tabs)
t_ignore  = ' \t\n'

# Error handling rule
def t_error(t):
    print "Illegal character '%s'" % t.value[0]
    t.lexer.skip(1)

# Build the lexer
lexer = lex.lex(debug=True,debuglog=log,errorlog=log)

spec = open(sys.argv[1]).read()

# Give the lexer some input
#lexer.input(spec)

#for tok in lexer:
#  print tok

def p_prog(p):
  '''prog : COMPONENTS COLON comps \
            MESSAGES COLON msgs \
            STATE COLON state \
            OPERATIONS COLON operations \
            INIT COLON init \
            HANDLERS COLON hdlrs \
            PROPERTIES COLON props
  '''
  p[0] = {'comps' : p[3], 'msgs' : p[6], 'state' : p[9], 'ops' : p[12],
          'init' : p[15], 'hdlrs' : p[18], 'props' : p[21]}

def p_comps(p):
  '''comps : comp comps
           | comp
  '''
  if len(p) == 3:
    p[0] = [p[1]] + p[2]
  else:
    p[0] = [p[1]]

def p_comp(p):
  'comp : ID STRING LPAREN stringlist RPAREN LPAREN idtypelist RPAREN'
  p[0] = {'tag' : p[1], 'cmd' : p[2], 'args' : p[4], 'idtypes' : p[7]}

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
    p[0] = dict(p[2], **p[1])
  elif len(p) == 2:
    p[0] = p[1]
  else:
    p[0] = {}

def p_stvar(p):
  '''stvar : ID COLON TYPE_D
           | ID COLON ID
  '''
  p[0] = {p[1] : p[3]}

def p_operations(p):
  '''operations : operation operations
                | operation
                |
  '''
  if len(p) == 3:
    p[0] = p[2]
    if 'files' in p[0]:
      p[0]['files'].add(p[1]['file'])
      p[0]['ops'].update(p[1]['op'])
  elif len(p) == 2:
    p[0] = {'files':Set([p[1]['file']]), 'ops':p[1]['op']}
  else:
    p[0] = {'files':Set([]), 'ops':{}}

def p_operation(p):
  'operation : ID DOT ID COLON funtype'
  p[0] = {'file':p[1], 'op':{p[3]:p[5]}}

def p_funtype(p):
  '''funtype : TYPE_D RARROW funtype
             | TYPE_D
  '''
  if len(p) == 4:
    p[0] = [p[1]] + p[3]
  else:
    p[0] = [p[1]]

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
  '''props : fullprop props
           | fullprop
           |
  '''
  if len(p) == 3:
    p[0] = [p[1]] + p[2]
  else:
    p[0] = [p[1]]

def p_hdlr(p):
  '''hdlr : WHEN ID COLON ID \
            SENDS ID LPAREN idlist RPAREN \
            RESPOND COLON cmd
  '''
  p[0] = {'cc' : p[2], 'ctag' : p[4], 'mtag' : p[6],
          'pl' : p[8], 'cmd'  : p[12]}

def p_cmd(p):
  '''cmd : nop
         | assign
         | seq
         | send
         | spawn
         | call
         | invokefd
         | invokestr
         | ite
         | lookup
  '''
  p[0] = p[1]

def p_nop(p):
  'nop : NOP'
  p[0] = {'type' : 'nop'}

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
  p[0] = {'type' : 'call', 'var' : p[1], 'expr' : p[4], 'args' : p[6]}

def p_invokefd(p):
  'invokefd : ID ASSIGN INVOKEFD expr LPAREN exprlist RPAREN'
  p[0] = {'type' : 'invokefd', 'var' : p[1], 'expr' : p[4], 'args' : p[6]}

def p_invokestr(p):
  'invokestr : ID ASSIGN INVOKESTR expr LPAREN exprlist RPAREN'
  p[0] = {'type' : 'invokestr', 'var' : p[1], 'expr' : p[4], 'args' : p[6]}

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

def p_fullprop(p):
  '''fullprop : ID COLON FORALL idlist COLON prop
              | ID COLON prop
  '''
  if len(p) == 7:
    p[6]['ids'] = p[4]
    p[0] = {'name':p[1], 'prop':p[6]}
  else:
    p[0] = {'name':p[1], 'prop':p[3]}

def p_prop(p):
  '''prop : tprop
          | niprop
  '''
  p[0] = p[1]

def p_tprop(p):
  '''tprop : LBRACE apat RBRACE IMMBEFORE LBRACE apat RBRACE
           | LBRACE apat RBRACE IMMAFTER LBRACE apat RBRACE
           | LBRACE apat RBRACE ENABLES LBRACE apat RBRACE
           | LBRACE apat RBRACE ENSURES LBRACE apat RBRACE
           | LBRACE apat RBRACE DISABLES LBRACE apat RBRACE
  '''
  p[0] = {'type':'tprop', 'prim' : p[4], 'pat1' : p[2], 'pat2' : p[6]}

def p_niprop(p):
  '''niprop : NOINTERFERE \
              HIGHCOMPS COLON cpatlist \
              HIGHVARS COLON idlist \
              HIGHCOMPLIST COLON cpatlist
  '''
  p[0] = {'type':'niprop', 'cpats' : p[4], 'stids' : p[7],
          'cspats' : p[10]}

def p_apat(p):
  '''apat : KSEND LPAREN cpat COMMA msgpat RPAREN
          | KRECV LPAREN cpat COMMA msgpat RPAREN
          | KSPAWN cpat
          | KCALL pat LPAREN patlist RPAREN pat
          | KINVOKEFD pat LPAREN patlist RPAREN pat
          | KINVOKESTR pat LPAREN patlist RPAREN pat
  '''
  p[0] = {'type' : p[1]}
  if p[0]['type'] == 'Send' or p[0]['type'] == 'Recv':
    p[0]['cpat'] = p[3]
    p[0]['mpat'] = p[5]
  elif p[0]['type'] == 'Spawn':
    p[0]['cpat'] = p[2]
  elif p[0]['type'] == 'Call':
    p[0]['cmd'] = p[2]
    p[0]['args'] = p[4]
    p[0]['fd'] = p[6]
  elif p[0]['type'] == 'InvokeFD':
    p[0]['cmd'] = p[2]
    p[0]['args'] = p[4]
    p[0]['fd'] = p[6]
  elif p[0]['type'] == 'InvokeStr':
    p[0]['cmd'] = p[2]
    p[0]['args'] = p[4]
    p[0]['str'] = p[6]

def p_msgpat(p):
  '''msgpat : ID LPAREN patlist RPAREN
            | WILDCARD
  '''
  if len(p) == 5:
    p[0] = {'id':p[1], 'pats':p[3]}
  else:
    p[0] = {'id':t_WILDCARD}

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
  '''expr : LPAREN expr OP expr RPAREN
          | LPAREN ID expr expr RPAREN
          | LPAREN ID expr RPAREN
          | LPAREN expr RPAREN
          | fieldexpr
          | idexpr
          | numexpr
          | stringexpr
  '''
  p[0] = {}
  if len(p) == 6:
    if type(p[3]) is str and re.match(t_OP, p[3]):
      p[0]['type'] = 'binop'
      p[0]['expr1'] = p[2]
      p[0]['expr2'] = p[4]
      p[0]['op'] = p[3]
    else:
      p[0]['type'] = 'binop'
      p[0]['expr1'] = p[3]
      p[0]['expr2'] = p[4]
      p[0]['op'] = p[2]
  elif len(p) == 4:
    p[0] = p[2]
  elif len(p) == 3:
    p[0]['type'] = 'unop'
    p[0]['expr'] = p[3]
    p[0]['op'] = p[2]
  else:
    p[0] = p[1]

def p_fieldexpr(p):
  'fieldexpr : ID DOT ID'
  p[0] = {'type' : 'field', 'id' : p[1], 'field' : p[3]}

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
  '''cpat : ID LPAREN patlist RPAREN
          | WILDCARD
  '''
  if len(p) == 5:
    p[0] = {'id' : p[1], 'pats' : p[3]}
  else:
    p[0] = {'id' : t_WILDCARD}

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
  '''pat : LPAREN pat OP pat RPAREN
         | WILDCARD
         | NUM
         | STRING
         | ID
  '''
  if len(p) == 6:
    p[0] = {'op':p[3], 'pat1':p[2], 'pat2':p[4]}
  else:
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

def p_idtypelist(p):
  '''idtypelist : idtype COMMA idtypelist
                | idtype
                |
  '''
  if len(p) == 4:
    p[0] = [p[1]] + p[3]
  elif len(p) == 2:
    p[0] = [p[1]]
  else:
    p[0] = []

def p_idtype(p):
  'idtype : ID COLON TYPE_D'
  p[0] = {'id' : p[1], 'type': p[3]}

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
parser = yacc.yacc(debug=True,debuglog=log,errorlog=log)

result = parser.parse(spec)
#print result

out = open(sys.argv[2], 'w')

def write_prelude(imports):
  out.write("Require Import String.\n")
  out.write("Require Import Reflex.\n")
  out.write("Require Import ReflexBase.\n")
  out.write("Require Import ReflexDenoted.\n")
  out.write("Require Import ReflexFin.\n")
  out.write("Require Import ReflexFrontend.\n")
  out.write("Require Import ReflexHVec.\n")
  out.write("Require Import ReflexIO.\n")
  out.write("Require Import ReflexVec.\n")
  out.write("Require Import Ascii.\n")
  for i in imports:
    out.write("Require Import " + i + ".\n")
  out.write("Open Scope string_scope.\n\n")
  out.write("Module SystemFeatures <: SystemFeaturesInterface.\n\n")

spec_to_desc = { 'str' : 'str_d', 'fd' : 'fd_d', 'num' : 'num_d' }
spec_to_desc_d = Set(['str_d', 'fd_d', 'num_d'])

def get_desc(x):
  return spec_to_desc[x]

def get_cdesc(x):
  if x in spec_to_desc:
    return 'Desc _ ' + spec_to_desc[x]
  elif x in spec_to_desc_d:
    return 'Desc _ ' + x
  else:
    return 'Comp _ ' + x

def arg_types_str(args):
  return "[" + "; ".join(map(get_desc, args)) + "]"

def gen_fin_notation(vard):
  for k, v in vard.items():
    out.write("Notation " + k + " := " + str(v['fin']) + "%fin (only parsing).\n")

# Returns a map from component type to a map from
# field to fin
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
  res = {}
  for c in comps:
    out.write("  | " + c['tag'] + "=> mk_compd\n")
    out.write("    \"" + c['tag'] + "\" " + c['cmd'] + " [" + "; ".join(c['args']) + "]\n")
    out.write("    (mk_vdesc " + arg_types_str(map(lambda t: t['type'], c['idtypes'])) + ")\n")
    res[c['tag']] = {t['id']:n for n, t in enumerate(c['idtypes'])}
  out.write("end.\n\n")
  return res

def process_msgs(msgs):
  out.write("Definition NB_MSG : nat := " + str(len(msgs)) + ".\n\n")
  out.write("Definition PAYD : vvdesc NB_MSG := mk_vvdesc\n")
  out.write("[\n")
  out.write(";\n".join(map(lambda m: "(\"" + m['tag'] + "\"," + arg_types_str(m['types']) + ")", msgs)))
  out.write("\n].\n\n")
  gen_fin_notation({m['tag']:{'fin':n} for n, m in enumerate(msgs)})
  out.write("\n")

def get_envd_seq(cmd, cont):
  return dict(cont(cmd['cmd1']), **cont(cmd['cmd2']))

def get_envd_spawn(cmd, cont):
  return {cmd['var'] : cmd['ctag']}

def get_envd_call(cmd, cont):
  return {cmd['var'] : 'fd_d'}

def get_envd_invokefd(cmd, cont):
  return {cmd['var'] : 'fd_d'}

def get_envd_invokestr(cmd, cont):
  return {cmd['var'] : 'str_d'}

def get_envd_ite(cmd, cont):
  return dict(cont(cmd['cmd1']), **cont(cmd['cmd2']))

def get_envd_lookup(cmd, cont):
  return dict(cont(cmd['cmd1']), **cont(cmd['cmd2']))

# compute the envd, ignoring variables added from CompLkup
# envd is a map from id to type
def get_envd_nolkup(cmd):
  return {
     'nop'       : lambda x ,y: {},
     'assign'    : lambda x ,y: {},
     'seq'       : get_envd_seq,
     'send'      : lambda x, y: {},
     'spawn'     : get_envd_spawn,
     'call'      : get_envd_call,
     'invokefd'  : get_envd_invokefd,
     'invokestr' : get_envd_invokestr,
     'ite'       : get_envd_ite,
     'lookup'    : get_envd_lookup
    }[cmd['type']](cmd, get_envd_nolkup)

# changes the vard to a map from id to a dictionary containing
# a type and a fin
def get_vard_fin(vard):
  return {v[0]:{'type':v[1],'fin':n} for n, v in enumerate(vard.items())}

# Assigns each cmd in the cmd tree an envd, using the
# input envd as the top level envd
def add_ctxt(cmd, envd, kstd, other):
  cmd['ctxt'] = {'envd' : envd, 'kstd' : kstd}
  cmd['ctxt'].update(other)
  if cmd['type'] == 'seq':
    add_ctxt(cmd['cmd1'], envd, kstd, other)
    add_ctxt(cmd['cmd2'], envd, kstd, other)
  elif cmd['type'] == 'ite':
    add_ctxt(cmd['cmd1'], envd, kstd, other)
    add_ctxt(cmd['cmd2'], envd, kstd, other)
  elif cmd['type'] == 'lookup':
    new_envd = envd.copy()
    if len(envd.values()) == 0:
      new_fin = 0
    else:
      new_fin = max(envd.values(), key=lambda x: x['fin'])['fin']+1
    new_envd[cmd['var']] = {'type' : cmd['ctag'],
                            'fin' : new_fin}
    add_ctxt(cmd['cmd1'], new_envd, kstd, other)
    add_ctxt(cmd['cmd2'], envd, kstd, other)

def get_type_list(vard):
  types_list = map(lambda x: get_cdesc(x['type']),
    sorted(vard.values(), key=lambda x: x['fin']))
  return '[' + ';'.join(types_list) + ']'

def process_init_envd(init, kstd, comp_map, ops):
  out.write("Definition IENVD : vcdesc COMPT := mk_vcdesc\n")
  out.write("  [\n")
  envd = get_vard_fin(get_envd_nolkup(init))
  add_ctxt(init, envd, kstd, {'comps':comp_map, 'ops':ops})
  types_list = map(lambda x: get_cdesc(x['type']),
    sorted(init['ctxt']['envd'].values(), key=lambda x: x['fin']))
  out.write("   " + ";\n   ".join(types_list))
  out.write("\n  ].\n\n")
  gen_fin_notation(envd)
  out.write("\n")

def process_kstd(state):
  out.write("Definition KSTD : vcdesc COMPT := mk_vcdesc\n")
  out.write("  [\n")
  state_with_fin = get_vard_fin(state)
  types_list = map(lambda x: get_cdesc(x['type']),
    sorted(state_with_fin.values(), key=lambda x: x['fin']))
  out.write("   " + ";\n   ".join(types_list))
  out.write("\n  ].\n\n")
  gen_fin_notation(state_with_fin)
  out.write("\n")
  return state_with_fin

def end_sys_features():
  out.write("End SystemFeatures.\n\n")
  out.write("Import SystemFeatures.\n\n")
  out.write("Module Language := MkLanguage(SystemFeatures).\n\n")
  out.write("Import Language.\n\n")
  out.write("Module Spec <: SpecInterface.\n\n")
  out.write("Include SystemFeatures.\n\n")

def get_op(op, ops, arity):
  builtin = {'==' : 'eq', '+' : 'add', '++' : 'cat'}
  if op in builtin:
    return builtin[op]
  elif op in ops:
    funtype = ops[op]
    return {1:'unop', 2:'binop'}[arity] + \
           '_' + funtype[len(funtype)-1] + ' _ _ ' + \
           ' '.join(map(lambda d: '(' + get_cdesc(d) + ')',
                        funtype[0:len(funtype)-1])) + \
           ' ' + op

def get_envd_str(envd):
  return 'mk_vcdesc ' + get_type_list(envd)

def get_envvar_term(ctxt, var, pref):
  return pref + 'envvar_t envd ' + \
         str(ctxt['envd'][var]['fin']) + \
         '%fin'

def get_envvar(ctxt, var, pref):
  return pref + 'envvar envd ' + \
         str(ctxt['envd'][var]['fin']) + \
         '%fin'

# ctxt contains things like envd, kstd, cc, etc.
def get_expr(expr, ctxt, pref):
  if expr['type'] == 'binop':
    return get_op(expr['op'], ctxt['ops'], 2) + \
           ' (' + get_expr(expr['expr1'], ctxt, pref) + \
           ') (' + get_expr(expr['expr2'], ctxt, pref) + ')'
  elif expr['type'] == 'unop':
    return get_op(expr['op'], ctxt['ops'], 1) + \
           ' (' + get_expr(expr['expr'], ctxt, pref) + ')'
  elif expr['type'] == 'field':
    if expr['id'] == ctxt['cc']:
      ct = ctxt['ctag']
      e = 'CComp _ _ _ _ _ _ _'
    elif expr['id'] in ctxt['envd']:
      ct = ctxt['envd'][expr['id']]['type']
      e = get_envvar_term(ctxt, expr['id'], pref)
    elif expr['id'] in ctxt['kstd']:
      ct = ctxt['kstd'][expr['id']]['type']
      e = 'StVar _ _ _ KSTD _ _ _ ' + expr['id']
    return 'cconf _ ' + ct + ' ' + str(ctxt['comps'][ct][expr['field']]) + \
           '%fin (' + e + ')'
  elif expr['type'] == 'id':
    if 'cc' in ctxt and expr['val'] == ctxt['cc']:
      return 'ccomp'
    elif expr['val'] in ctxt['envd']:
      return get_envvar(ctxt, expr['val'], pref)
    elif 'mvars' in ctxt and expr['val'] in ctxt['mvars']:
      return 'mvar ' + ctxt['mtag'] + ' ' + \
             str(ctxt['mvars'].index(expr['val'])) + '%fin'
    elif expr['val'] in ctxt['kstd']:
      return 'stvar ' + expr['val']
  elif expr['type'] == 'num':
    return pref + 'nlit (num_of_nat ' + \
           str(expr['val']) + ')'
  elif expr['type'] == 'string':
    return pref + 'slit (str_of_string ' + \
           str(expr['val']) + ')'

def get_iexpr(expr, ctxt):
  return get_expr(expr, ctxt, 'i_')

def get_hexpr(expr, ctxt):
  return get_expr(expr, ctxt, '')

def get_oexpr(expr, ctxt, expr_fun):
  if expr == t_WILDCARD:
    return 'None'
  else:
    return 'Some (' + expr_fun(expr, ctxt) + ')'

def get_expr_vec(lexpr, expr_fun, ctxt):
  return reduce(lambda acc, h: '(' + expr_fun(h, ctxt) + ', ' + acc + ')',
    lexpr[::-1], 'tt')

def get_nop(cmd, cont, expr_fun):
  return 'nop'

def get_assign(cmd, cont, expr_fun):
  return 'stupd _ envd ' + cmd['var'] + \
         ' (' + expr_fun(cmd['expr'], cmd['ctxt']) + ')'

def get_seq(cmd, cont, expr_fun):
  return '  seq (' + cont(cmd['cmd1'], expr_fun) + ') (\n' \
         + cont(cmd['cmd2'], expr_fun) + ')'

def get_send(cmd, cont, expr_fun):
  return 'send (' + expr_fun(cmd['expr'], cmd['ctxt']) + \
         ') ' + cmd['mtag'] + ' ' + \
         get_expr_vec(cmd['pl'], expr_fun, cmd['ctxt'])

def get_spawn(cmd, cont, expr_fun):
  return 'spawn _ envd ' + cmd['ctag'] + ' ' + \
         get_expr_vec(cmd['cfg'], expr_fun, cmd['ctxt']) + ' ' + \
         str(cmd['ctxt']['envd'][cmd['var']]['fin']) + '%fin' + \
         ' (Logic.eq_refl _)'

def get_call(cmd, cont, expr_fun):
  return 'call _ envd (' + expr_fun(cmd['expr'], cmd['ctxt']) + ') [' + \
         ';'.join(map(lambda e: expr_fun(e, cmd['ctxt']), cmd['args'])) \
         + '] ' + str(cmd['ctxt']['envd'][cmd['var']]['fin']) + '%fin' + \
         ' (Logic.eq_refl _)'

def get_invokefd(cmd, cont, expr_fun):
  return 'Reflex.InvokeFD _ _ _ _ _ envd (' + \
         expr_fun(cmd['expr'], cmd['ctxt']) + ') [' + \
         ';'.join(map(lambda e: expr_fun(e, cmd['ctxt']), cmd['args'])) \
         + '] ' + str(cmd['ctxt']['envd'][cmd['var']]['fin']) + '%fin' + \
         ' (Logic.eq_refl _)'

def get_invokestr(cmd, cont, expr_fun):
  return 'Reflex.InvokeStr _ _ _ _ _ envd (' + \
         expr_fun(cmd['expr'], cmd['ctxt']) + ') [' + \
         ';'.join(map(lambda e: expr_fun(e, cmd['ctxt']), cmd['args'])) \
         + '] ' + str(cmd['ctxt']['envd'][cmd['var']]['fin']) + '%fin' + \
         ' (Logic.eq_refl _)'

def get_ite(cmd, cont, expr_fun):
  return 'ite (' + expr_fun(cmd['cond'], cmd['ctxt']) + ')\n' + \
          '    (\n' + '      ' + cont(cmd['cmd1'], expr_fun) + \
          '    )(\n' + '      ' + cont(cmd['cmd2'], expr_fun) + \
          '    )'

def get_lookup(cmd, cont, expr_fun):
  return 'complkup (envd:=envd) ' \
         + '(mk_comp_pat _ _ ' + cmd['ctag'] + ' ' + \
         get_expr_vec(cmd['cfg'],
           lambda e, ctxt: get_oexpr(e, ctxt, expr_fun),
           cmd['ctxt']) + ')\n' + \
         '    (let envd :=' + get_envd_str(cmd['cmd1']['ctxt']['envd']) + ' in\n' + \
         '      ' + cont(cmd['cmd1'], expr_fun) + \
         '    )(\n' + '      ' + cont(cmd['cmd2'], expr_fun) + \
         '    )'

def get_cmd(cmd, expr_fun):
  return {
    'nop'       : get_nop,
    'assign'    : get_assign,
    'seq'       : get_seq,
    'send'      : get_send,
    'spawn'     : get_spawn,
    'call'      : get_call,
    'invokefd'  : get_invokefd,
    'invokestr' : get_invokestr,
    'ite'       : get_ite,
    'lookup'    : get_lookup
  }[cmd['type']](cmd, get_cmd, expr_fun)

def process_init(init):
  out.write("Definition INIT : init_prog PAYD COMPT COMPS KSTD IENVD :=\n")
  out.write("let envd := IENVD in\n")
  out.write('(exist _ (' + get_cmd(init, get_iexpr) + ')\n')
  out.write('  (conj (Logic.eq_refl _) (Logic.eq_refl _))).\n\n')

def process_hdlr(hdlr, kstd, comp_map, ops):
  envd = get_vard_fin(get_envd_nolkup(hdlr['cmd']))
  add_ctxt(hdlr['cmd'], envd, kstd,
           {'comps':comp_map, 'ops':ops, 'cc':hdlr['cc'],
            'ctag':hdlr['ctag'], 'mtag':hdlr['mtag'],'mvars':hdlr['pl']})
  out.write('|' + hdlr['ctag'] + ', ' + hdlr['mtag'] + ' =>\n')
  out.write('let envd := ' + get_envd_str(hdlr['cmd']['ctxt']['envd']) + ' in\n')
  out.write('[[ envd :\n')
  out.write('  exist _ (' + get_cmd(hdlr['cmd'], get_hexpr) + ') (Logic.eq_refl _)\n')
  out.write(']]\n')

def process_hdlrs(hdlrs, kstd, comp_map, ops):
  out.write("Open Scope hdlr.\n")
  out.write("Definition HANDLERS : handlers PAYD COMPT COMPS KSTD :=\n")
  out.write("  fun t ct =>\n")
  out.write("    match ct as _ct, t as _t return\n")
  out.write("      {prog_envd : vcdesc COMPT & hdlr_prog PAYD COMPT COMPS KSTD _ct _t prog_envd}\n")
  out.write("    with\n")
  for hdlr in hdlrs:
    process_hdlr(hdlr, kstd, comp_map, ops)
  out.write("| _, _ =>\n")
  out.write("  [[ mk_vcdesc [] : exist _ nop (Logic.eq_refl _)]]\n")
  out.write("end.\n")
  out.write("Close Scope hdlr.\n")

def finish_spec():
  out.write("End Spec.\n\n")
  out.write("Module Main := MkMain(Spec).\n")

def get_pat(pat):
  if type(pat) is dict:
    op = {'++':'List.app'}[pat['op']]
    return op + ' (' + get_pat(pat['pat1']) + ') (' \
           + get_pat(pat['pat2']) + ')'
  else:
    if re.match(r'\d+', pat):
      return 'num_of_nat ' + pat
    elif re.match(t_STRING, pat):
      return 'str_of_string ' + pat
    else:
      return pat

def get_opat(pat):
  if pat == t_WILDCARD:
    return 'None'
  else:
    return 'Some (' + get_pat(pat) + ')'

def get_opat_vec(pats):
  return reduce(lambda acc, h: '(' + get_opat(h) + ', ' + acc + ')',
    pats[::-1], 'tt')

def get_conc_pat(pat):
  return 'Build_conc_pat COMPT COMPS ' + pat['id'] \
         + ' ' + get_opat_vec(pat['pats'])

def get_oconc_pat(pat):
  if pat['id'] == t_WILDCARD:
    return 'None'
  else:
    return 'Some (' + get_conc_pat(pat) + ')'

def get_msg_pat(pat):
  if pat['id'] == t_WILDCARD:
    return 'None'
  else:
    return 'Some (Build_opt_msg PAYD ' + pat['id'] \
           + ' ' + get_opat_vec(pat['pats']) + ')'

def get_pat_str(pat):
  if pat['type'] == 'Spawn':
    return 'KOExec PAYD COMPT COMPS None None ' + \
           '(' + get_oconc_pat(pat['cpat']) + ')'
  elif pat['type'] == 'Recv' or pat['type'] == 'Send':
    return 'KO' + pat['type'] + ' PAYD COMPT COMPS ' + \
           '(' + get_oconc_pat(pat['cpat']) + ')' + \
           '(' + get_msg_pat(pat['mpat']) + ')'
  elif pat['type'] == 'Call':
    return 'KOCall PAYD COMPT COMPS ' + \
           '(' + get_opat(pat['cmd']) + ') ' + \
           '(Some (' + '::'.join(map(get_opat, pat['args']) + ['nil']) + \
           ')) (' + get_opat(pat['fd']) + ')'
  elif pat['type'] == 'InvokeFD':
    return 'KOInvokeFD PAYD COMPT COMPS ' + \
           '(' + get_opat(pat['cmd']) + ') ' + \
           '(Some (' + '::'.join(map(get_opat, pat['args']) + ['nil']) + \
           ')) (' + get_opat(pat['fd']) + ')'
  elif pat['type'] == 'InvokeStr':
    return 'KOInvokeStr PAYD COMPT COMPS ' + \
           '(' + get_opat(pat['cmd']) + ') ' + \
           '(Some (' + '::'.join(map(get_opat, pat['args']) + ['nil']) + \
           ')) (' + get_opat(pat['str']) + ')'

def get_clblr(cpats, num_cts):
  res = 'fun c : comp COMPT COMPS => match c with\n'
  for cpat in cpats:
    res += '| Build_comp ' + cpat['id'] + ' _ cfg =>\n'
    res += '  let cfgd := comp_conf_desc COMPT COMPS ' + cpat['id'] + ' in\n'
    res += '  @shvec_match _ (projT1 cfgd) (projT2 cfgd) sdenote_desc sdenote_desc_conc_pat elt_match\n'
    res += '              cfg (' + get_opat_vec(cpat['pats']) + ')\n'
  if len(cpats) < num_cts:
    res += '| _ => false\n'
  res += 'end'
  return res

#  return 'fun c => existsb (fun cp => Reflex.match_comp COMPT COMPTDEC COMPS cp c) ' + '\n(' + \
 #        '::'.join(map(get_conc_pat, cpats) + ['nil']) + ')'

def get_vlblr(stids):
  return 'fun f => match f with ' + \
         ' | '.join(map(lambda i: i + ' => true', stids)) + \
         ' | _ => false end'

def get_foralls(prop, extra):
  ids = extra
  if 'ids' in prop:
    ids += prop['ids']
  if len(ids) == 0:
    return ''
  else:
    return 'forall ' + ' '.join(ids) + ','

def process_niprop(prop, pout, num_cts):
  pout.write("Theorem ni : " + get_foralls(prop, []) + '\n')
  pout.write("let comp_lblr :=\n")
  pout.write(get_clblr(prop['cpats'], num_cts) + '\n')
  pout.write("in\n")
  pout.write("let vlblr :=\n")
  pout.write(get_vlblr(prop['stids']) + '\n')
  pout.write("in\n")
  pout.write("let comp_list_lblr :=\n")
  pout.write(get_clblr(prop['cspats'], num_cts) + '\n')
  pout.write("in\n")
  pout.write("  NI PAYD COMPT COMPTDEC COMPS\n")
  pout.write("  IENVD KSTD INIT HANDLERS comp_lblr vlblr comp_list_lblr.\n")
#  pout.write("  (" + get_clblr(prop['cpats']) + ')\n')
#  pout.write("  (" + get_vlblr(prop['stids']) + ')\n')
#  pout.write("  (" + get_clblr(prop['cspats']) + ').\n')
  pout.write("Proof.\n")
  pout.write("  Time solve[ni].\n")
  pout.write("Time Qed.")

def process_tprop(prop, pout):
  pout.write("Theorem t : " + get_foralls(prop, ['st', 'tr']) + '\n')
  pout.write("  Reach PAYD COMPT COMPTDEC COMPS KSTD IENVD INIT HANDLERS st ->\n")
  pout.write("  ktr _ _ _ _ st = inhabits tr ->\n")
  pout.write("  " + prop['prim'] + " PAYD COMPT COMPS COMPTDEC\n")
  pout.write("    (" + get_pat_str(prop['pat1']) + ")\n")
  pout.write("    (" + get_pat_str(prop['pat2']) + ")\n")
  pout.write("    tr.\n")
  pout.write("Proof.\n")
  pout.write("  Time solve[crush].\n")
  pout.write("Time Qed.")

def process_props(props, num_cts):
  for prop in props:
    pout = open("Policy" + prop['name'] + ".v", 'w')
    pout.write("Require Import String.\n")
    pout.write("Require Import Reflex ReflexBase.\n")
    pout.write("Require Import PolLang ActionMatch.\n")
    pout.write("Require Import Kernel.\n")
#    pout.write("Local Opaque str_of_string.\n")
    pout.write("Import SystemFeatures Language Spec.\n")
    if prop['prop']['type'] == 'tprop':
      process_tprop(prop['prop'], pout)
    else:
      pout.write("Require Import NIInputTree ReflexHVec ReflexIO.\n")
      process_niprop(prop['prop'], pout, num_cts)

write_prelude(result['ops']['files'])
process_msgs(result['msgs'])
comp_map = process_comps(result['comps'])
kstd = process_kstd(result['state'])
process_init_envd(result['init'], kstd, comp_map, result['ops']['ops'])
end_sys_features()
process_init(result['init'])
process_hdlrs(result['hdlrs'], kstd, comp_map, result['ops']['ops'])
finish_spec()
process_props(result['props'], len(comp_map.keys()))
