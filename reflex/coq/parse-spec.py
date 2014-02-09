import re
import sys

fspec = open(sys.argv[1])
spec = fspec.read()
fout = open("Spec.v", "w")

msgs_pat = re.compile("Messages\s*\{(?P<msgs>.*?)\}", re.DOTALL)
msg_pat = re.compile("(?P<type>\w*)\((?P<args>.*?)\)")
comps_pat = re.compile("Components\s*\{(?P<comps>.*?)\}", re.DOTALL)
comp_pat = re.compile("(?P<type>\w*)\((?P<args>.*?)\)\s*\"(?P<cmd>.*?)\" (?P<cmd_args>\[.*?\])")
state_pat = re.compile("State\s*\{(?P<state>.*?)\}", re.DOTALL)
stvar_pat = re.compile("(?P<name>\w*)\s*:\s*(?P<type>.*?);")

spec_to_desc = { "string" : "str_d", "fd" : "fd_d", "num" : "num_d" }

def arg_types_str(args):
  res = "["
  for s in args.split(","):
    if s in spec_to_desc:
      res = res + spec_to_desc[s] + ";"
  return res[0:len(res)-1] + "]"

def cdesc_str(stype):
  s = stype.split()
  if len(s) == 2:
    if s[0] == "comp":
      return "Comp _ " + s[1]
    else:
      print "Fail"
  elif len(s) == 1:
    if s[0] in spec_to_desc:
      return "Desc _ " + spec_to_desc[s[0]]
    else:
      print "Fail"
  else:
    print "Fail"

fout.write("Require Import String.\n")
fout.write("Require Import Reflex.\n")
fout.write("Require Import ReflexBase.\n")
fout.write("Require Import ReflexDenoted.\n")
fout.write("Require Import ReflexFin.\n")
fout.write("Require Import ReflexFrontend.\n")
fout.write("Require Import ReflexHVec.\n")
fout.write("Require Import ReflexIO.\n")
fout.write("Require Import ReflexVec.\n")
fout.write("Open Scope string_scope.\n")
fout.write("Module SystemFeatures <: SystemFeaturesInterface.\n\n")

mspec = re.search(msgs_pat, spec)
if mspec:
  mspecs = re.findall(msg_pat, mspec.group("msgs"))
  fout.write("Definition NB_MSG : nat := " + str(len(mspecs)) + ".\n\n")
  fout.write("Definition PAYD := mk_vvdesc\n")
  fout.write("[\n")
  msg_list = ""
  for m in mspecs:
    msg_list = msg_list + "(\"" + m[0] + "\"," + arg_types_str(m[1]) + ");\n"
  fout.write(msg_list[0:len(msg_list)-2])
  fout.write("\n].\n\n")
  fin = 0
  for m in mspecs:
    fout.write("Notation " + m[0] + " := " + str(fin) + "%fin (only parsing).\n")
    fin = fin + 1
  fout.write("\n")
else:
  print "Fail"

cspec = re.search(comps_pat, spec)
if cspec:
  cspecs = re.findall(comp_pat, cspec.group("comps"))
  fout.write("Inductive COMPT' : Type :=\n")
  for c in cspecs:
    fout.write("|" + str(c[0]) + "\n")
  fout.write(".\n\n")
  fout.write("Definition COMPT := COMPT'.\n\n")
  fout.write("Definition COMPTDEC : forall (x y : COMPT), decide (x = y).\n")
  fout.write("Proof. decide equality. Defined.\n\n")
  fout.write("Definition COMPS (t : COMPT) : compd :=\n")
  fout.write("  match t with\n")
  for c in cspecs:
    fout.write("| " + c[0] + "=> mk_compd\n")
    fout.write("    \"" + c[0] + "\" \"" + c[2] + "\" " + c[3] + "\n")
    fout.write("(mk_vdesc " + arg_types_str(c[1]) + ")\n")
  fout.write("end.\n\n")
else:
  print "Fail"

stspec = re.search(state_pat, spec)
if stspec:
  varspecs = re.findall(stvar_pat, stspec.group("state"))
  fout.write("Definition KSTD : vcdesc COMPT := mk_vcdesc\n")
  fout.write("[\n")
  desc_list = ""
  for v in varspecs:
    desc_list = desc_list + cdesc_str(v[1]) + ";\n"
  fout.write(desc_list[0:len(desc_list)-2])
  fout.write("].\n\n")
  fin = 0
  for v in varspecs:
    fout.write("Notation " + v[0] + " := " + str(fin) + "%fin (only parsing).\n")
    fin = fin + 1
  fout.write("\n")
else:
  print "Fail"

fout.write("End SystemFeatures.\n")
