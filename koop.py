from mimetypes import init
from tracemalloc import start

import angr
import argparse
from angrutils import plot_cfg, hook0, set_plot_style
import bingraphvis
import filecmp
import os
import subprocess
import networkx as nx
from stmtInfo import stmtInfo



class Info(object):
    def __init__(self):
        self.args = None

        self.binaryfile =None
        self.asmfile = None
        self.picflag = None

        self.project = None
        self.cfg = None
        self.tempVar = dict()
        self.regs = dict()
        self.mem = dict()
        self.storeIns = []
        self.func = None
        self.esp = 24
        self.ebp = 28
        self.debug = False
        self.curr_asm_ins = None
        
			

global p
p = Info()


def op_data(operator,d1=None,d2=None,d3=None,d4=None):
	
	if(operator == 'Iop_Add32'):
		return d1 + d2

def check(flag1,flag2):
	if flag1 and flag2 :
		return True
	else:
		return False
		
def parse_data(expr,tempVar_map):

	flag = False
	val = None
	
	if(p.debug) : 
		print(expr.tag)
	if expr.tag == "Iex_Const" :
		flag=True
		
		val = (expr.con.value)
			
	if expr.tag == 'Iex_RdTmp' :
		if expr.tmp in tempVar_map :
			flag=True
			val = tempVar_map[expr.tmp]	
	if expr.tag == 'Iex_Get' :
		if expr.offset in p.regs :
			flag = True 
			val = p.regs[expr.offset] 
		else :
			print("loading from uninitialized register")
			
	if expr.tag == 'Iex_Load' :
		flag1,addr = parse_data(expr.addr,tempVar_map)	
		if flag1 :
			flag = True
			val = 0
			if addr not in p.storeIns :
				print("Loading addr : " + str(hex(addr)))
				print("at " + hex(p.curr_asm_ins))
				loading_offset_addr = 0x100000000-int(addr)
				print("ebp = esp "+str(p.regs[28]))
				print("Use of Uninitialized Mem loc at esp - " + hex(loading_offset_addr))
			
						
		
	if expr.tag == 'Iex_Binop' :
		flag1,data1 = parse_data(expr.args[0],tempVar_map)
		flag2,data2 = parse_data(expr.args[1],tempVar_map)
		op = expr.op
		if(op == 'Iop_Add32' and check(flag1,flag2) ):
			flag = True
			val = data1+data2
		if(op == 'Iop_Sub32' and check(flag1,flag2)) :
			flag = True
			val = data1-data2
		if(op =='Iop_And32' and check(flag1,flag2)) :
			flag=True
			val = data1 & data2

		#print(op)
	if expr.tag == 'Iex_Unop' :
		flag1,data1 = parse_data(expr.args[0],tempVar_map)
		if flag1 :
			val = data1
	if(p.debug):	
		print(flag,val)
	return (flag,val)
  	

def build_CFG():

    main_addr = p.project.loader.main_object.get_symbol('main').rebased_addr
    p.cfg = p.project.analyses.CFGEmulated(starts=[main_addr],initial_state = p.project.factory.blank_state())
    plot_cfg(p.cfg, "example_cfg_asm", asminst=True, vexinst=False, debug_info=False, remove_imports=True, remove_path_terminator=True)
    plot_cfg(p.cfg, "example_cfg_vex", asminst=False, vexinst=True, debug_info=False, remove_imports=True, remove_path_terminator=True)
    nodes = p.cfg.graph.nodes
    p.regs[p.esp]=0
    p.regs[p.ebp]=0
    #p.regs[p.ebp]=0
    nodes_list = list(nodes)
    for i in range(len(nodes)) :
        node = nodes_list[i]
        try:
            stmts = node.block.vex.statements
        except:
            stmts = []
        
        tempVar_map = dict()
        
        p.curr_asm_ins = None
       
        for stmt in stmts :
          #print(stmt.tag)
          stmtinfo = stmtInfo(stmt)
          #print(stmtinfo)
         
          if(p.debug):
	          print(stmt)
          
          if(p.debug):
	          print(stmt.tag)
	          
          if stmt.tag == 'Ist_IMark' :
            p.curr_asm_ins = stmt.addr        
          if stmt.tag == 'Ist_Put' :
            flag,data = parse_data(stmt.data,tempVar_map)
            #print(flag,data)
            if flag and data != None :
              p.regs[stmt.offset] = data
            	# if stmt.offset == 28 :
            	# 	p.regs[28] = 0
            	# else :
	            # 	p.regs[stmt.offset] = data
       
          if stmt.tag == 'Ist_WrTmp':
            flag,data = parse_data(stmt.data,tempVar_map)
            #print(flag,data)
            if flag and data != None :
            	tempVar_map[stmt.tmp] = data
          
          if stmt.tag == 'Ist_Store' :
            flag,addr = parse_data(stmt.addr,tempVar_map)
            flag1,data = parse_data(stmt.data,tempVar_map)
            
            if flag :
            	    print("storing addr : " + str(hex(addr)))
            	    p.storeIns.append(addr)
          if(p.debug) : 	
	          print(tempVar_map)
          if(p.debug):
        	  print(p.regs)
          if(p.debug):
        	  print(p.storeIns)
          if(p.debug):
	          print('\n\n')    	
						
						


					
				
    
    


	


def disassemble():
	p.binaryfile = os.path.realpath(p.args.input)

	# generate objdump file
	p.asmfile = p.binaryfile + "_asm"
	#print(info.asmfile)
	tmpfile = "/tmp/" + os.path.basename(p.asmfile)
	#print(tmpfile)
	comm = "objdump -d " + p.binaryfile + " > " + tmpfile
	os.system(comm)
	if os.path.exists(tmpfile):
		if (os.path.exists(p.asmfile) and not filecmp.cmp(tmpfile, p.asmfile)) or not os.path.exists(p.asmfile):
			comm = "objdump -d " + p.binaryfile + " > " + p.asmfile
			os.system(comm)


def parse_parameters():
	parser = argparse.ArgumentParser(description='SelectiveTaint static analysis')
	parser.add_argument("-input", help = "input enclave binary file", type=str, required=True)
	parser.add_argument("-debug", help = "to debug file", type=str, required=True)
	p.args = parser.parse_args()

def load_binary():
	file_command_return_string = subprocess.check_output(['file', p.args.input]).decode('utf-8')
	#p.debug = True
	#if info.args.input.endswith(".so"):
	if "shared object" in file_command_return_string and "dynamically linked" in file_command_return_string:
		p.picflag = 1
	else:
		p.picflag = 0

	try:
		p.project = angr.Project(p.args.input,load_options={'auto_load_libs': False})
	except:
		p.picflag = 0
		p.project = angr.Project(p.args.input, 
			main_opts = {'backend': 'blob'},
			load_options={'auto_load_libs': False})
    

parse_parameters()
load_binary()
disassemble()
build_CFG()
